module Failfree
  ( proveNonFailingFuncs, loadAnalysisWithImports
  ) where

import Control.Monad               ( unless, when )
import Control.Monad.IO.Class      ( liftIO )
import Control.Monad.Trans.Class   ( lift )
import Control.Monad.Trans.State   ( evalStateT, get, gets, put )
import Data.List                   ( find, maximum, minimum )

import Analysis.ProgInfo           ( ProgInfo, combineProgInfo, lookupProgInfo )
import Analysis.TotallyDefined     ( siblingCons )
import Analysis.Types              ( Analysis )
import CASS.Server                 ( analyzeGeneric, analyzePublic )
import Contract.Names              ( decodeContractQName, toNonFailQName )
import FlatCurry.Annotated.Goodies
import FlatCurry.Types             ( showQName )
import Language.SMTLIB.Goodies
import qualified Language.SMTLIB.Types as SMT
import RW.Base                     ( ReadWrite )

import CheckSMT
import Common
import Curry2SMT
import ESMT
import FlatCurry.Typed.Goodies
import FlatCurry.Typed.Types
import ToolOptions
import TransState
import VerifierState

---------------------------------------------------------------------------
-- Prove that a list of defined functions is fail free (w.r.t. their
-- non-fail conditions).
proveNonFailingFuncs :: TAProg -> VStateM ()
proveNonFailingFuncs prog = do
  siblingconsinfo <- lift $ loadAnalysisWithImports siblingCons prog
  mapM_ (proveNonFailingFunc siblingconsinfo) $ progFuncs prog

  -- Loads CASS analysis results for a module and its imported entities.
loadAnalysisWithImports ::
  (Read a, Show a, ReadWrite a, Eq a) => Analysis a -> TAProg -> IO (ProgInfo a)
loadAnalysisWithImports analysis prog = do
  maininfo <- analyzeGeneric analysis (progName prog)
                >>= return . either id error
  impinfos <- mapM (\m -> analyzePublic analysis m >>=
                                                     return . either id error)
                    (progImports prog)
  return $ foldr combineProgInfo maininfo impinfos

-- Prove that a function is fail free (w.r.t. their non-fail condition).
proveNonFailingFunc :: ProgInfo [(QName,Int)] -> TAFuncDecl -> VStateM ()
proveNonFailingFunc siblingconsinfo fdecl =
  unless (isContractOp (funcName fdecl) || isProperty fdecl) $ do
    printWhenIntermediate $
      "Operation to be analyzed: " ++ snd (funcName fdecl)
    incNumAllInStats
    let efdecl = etaExpandFuncDecl fdecl
    proveNonFailingRule siblingconsinfo (funcName efdecl) (funcType efdecl)
                        (funcRule efdecl)

-- Prove that a function rule is fail free (w.r.t. their non-fail condition).
-- The rule is in eta-expanded form.
proveNonFailingRule :: ProgInfo [(QName,Int)] -> QName -> TypeExpr -> TARule
                    -> VStateM ()
proveNonFailingRule _ qn ftype (AExternal _ _) = do
  let atypes = argTypes ftype
      args   = zip [1 .. length atypes] atypes
  nfcond <- evalStateT (nonfailPreCondExpOf qn ftype args) emptyTransState
  unless (nfcond == true) incNumNFCInStats
proveNonFailingRule siblingconsinfo qn@(_,fn) ftype (ARule _ rargs rhs) = do
  let st = makeTransState (maximum (0 : map fst rargs ++ allVars rhs) + 1)
            (map (\(i,(x,y)) -> (x, y, Just (qn, i, 1)))
                 (zip [1..] rargs))
  (flip evalStateT) st $ do
    -- compute non-fail precondition of operation:
    precondformula <- nonfailPreCondExpOf qn ftype rargs
    setAssertion precondformula
    unless (precondformula == true) $ lift incNumNFCInStats
    -- verify only if the precondition is different from always failing:
    unless (precondformula == false) $ proveNonFailExp rhs
 where
  proveNonFailExp exp = case exp of
    AComb _ ct (qf,qfty) args -> do
      mapM_ proveNonFailExp args
      when (isCombTypeFuncPartCall ct) $ do
        nfconds <- lift $ gets $ nfConds . trInfo
        let qnnonfail = toNonFailQName qf
        maybe
          (return ()) -- h.o. call nonfailing if op. has no non-fail cond.
          (const $ lift $ do
            let reason = "due to call '" ++ ppTAExpr exp ++ "'"
            addFailedFuncToStats fn reason
            printWhenIntermediate $
              fn ++ ": POSSIBLY FAILING CALL OF '" ++ snd qf ++ "'")
          (find (\fd -> funcName fd == qnnonfail) nfconds)
      when (ct==FuncCall) $ do
        lift $ printWhenIntermediate $ "Analyzing call to " ++ snd qf
        precond <- getAssertion
        (bs,_)   <- normalizeArgs args
        unless (fst qf == "Prelude") $ setNameOfVars qf $ map fst bs
        bindexps <- mapM (binding2SMT True) bs
        let callargs = zip (map fst bs) (map annExpr args)
        nfcondcall <- nonfailPreCondExpOf qf qfty callargs
        -- TODO: select from 'bindexps' only demanded argument positions
        valid <- if nfcondcall == true
                   then return (Just True) -- true non-fail cond. is valid
                   else do
                     lift incFailTestInStats
                     let title = "SMT script to verify non-failing call of '" ++
                                 snd qf ++ "' in function '" ++ fn ++ "'"
                     checkNonFailFunc title precond (tand bindexps) nfcondcall
        if valid == Just True
          then lift $ printWhenIntermediate $
                 fn ++ ": NON-FAILING CALL OF '" ++ snd qf ++ "'"
          else lift $ do
            let reason = if valid == Nothing
                           then "due to SMT error"
                           else "due to call '" ++ ppTAExpr exp ++ "'"
            addFailedFuncToStats fn reason
            printWhenIntermediate $
              fn ++ ": POSSIBLY FAILING CALL OF '" ++ snd qf ++ "'"
    ACase _ _ e brs -> do
      proveNonFailExp e
      maybe
       (do -- check a case expression for missing constructors:
          freshvar <- getFreshVar
          let freshtypedvar = (freshvar, annExpr e)
          be <- binding2SMT True (freshvar,e)
          addToAssertion be
          addVarTypes [freshtypedvar]
          let misscons = missingConsInBranch siblingconsinfo brs
          st <- get -- use same state to prove missing and non-fail branches
          mapM_ (verifyMissingCons freshtypedvar exp) misscons
          put st
          mapM_ (proveNonFailBranch freshtypedvar) brs
       )
       (\ (fe,te) -> do
           -- check a Boolean case with True/False branch:
           be <- pred2SMT e
           st <- get
           addToAssertion (tnot be)
           proveNonFailExp fe
           put st
           addToAssertion be
           proveNonFailExp te
       )
       (testBoolCase brs)
    AOr _ e1 e2 -> do st <- get -- use same state for both branches
                      proveNonFailExp e1
                      put st
                      proveNonFailExp e2
    ALet _ bs e -> do (rbs,re) <- renameLetVars bs e
                      mapM_ proveNonFailExp $ map snd rbs
                      proveNonFailExp re
    AFree _ fvs e -> do (_,re) <- renameFreeVars fvs e
                        proveNonFailExp re
    ATyped _ e _ -> proveNonFailExp e
    AVar _ _ -> return ()
    ALit _ _ -> return ()

  -- verify whether a variable (2. argument) can have the constructor (3. arg.)
  -- as a value w.r.t. the collected assertions
  verifyMissingCons (var,vartype) exp (cons,_) = do
    let title = "check missing constructor case '" ++ snd cons ++
                "' in function '" ++ fn ++ "'"
    lift $ printWhenIntermediate $
      title ++ "\nVAR: " ++ show (var,vartype) ++ "\nCASE:: " ++
      show (unAnnExpr exp)
    lift $ incPatTestInStats
    precond  <- getAssertion
    valid <- checkNonFailFunc ("SMT script to " ++ title) precond true
               (tnot (constructorTest False cons (tvar var) vartype))
    unless (valid == Just True) $ lift $ do
      let reason = if valid == Nothing
                     then "due to SMT error"
                     else "maybe not defined on constructor '" ++
                          showQName cons ++ "'"
      addFailedFuncToStats fn reason
      printWhenIntermediate $
        "POSSIBLY FAILING BRANCH in function '" ++ fn ++
        "' with constructor " ++ snd cons

  proveNonFailBranch (var,vartype) branch = do
    ABranch p e <- renamePatternVars branch
    -- set pattern type correctly (important for [] pattern)
    let bpat = pat2SMT (setAnnPattern vartype p)
    addToAssertion (tvar var =% bpat)
    proveNonFailExp e

-- Returns the constructors (name/arity) which are missing in the given
-- branches of a case construct.
missingConsInBranch :: ProgInfo [(QName,Int)] -> [TABranchExpr] -> [(QName,Int)]
missingConsInBranch _ [] =
  error "missingConsInBranch: case with empty branches!"
missingConsInBranch _ (ABranch (ALPattern _ _) _ : _) =
  error "TODO: case with literal pattern"
missingConsInBranch siblingconsinfo
                    (ABranch (APattern _ (cons,_) _) _ : brs) =
  let othercons = maybe (error $ "Sibling constructors of " ++
                                 showQName cons ++ " not found!")
                        id
                        (lookupProgInfo cons siblingconsinfo)
      branchcons = map (patCons . branchPattern) brs
  in filter ((`notElem` branchcons) . fst) othercons

-- Returns the conjunction of the non-failure condition and precondition
-- (if the tool option `contract` is set) expression for a given operation
-- and its arguments (which are assumed to be variable indices).
-- Rename all local variables by adding the `freshvar` index to them.
nonfailPreCondExpOf :: QName -> TypeExpr -> [(Int,TypeExpr)]
                    -> TransStateM SMT.Term
nonfailPreCondExpOf qf ftype args = do
  isCon <- lift $ getOption optConFail
  if isCon
    then do
      (fvars,nfcond) <- nonfailCondExpOf qf ftype args
      precond <- preCondExpOf qf (args ++ fvars)
      -- simplify term in order to check later for trivial precondition
      return (simpTerm (tand [nfcond,precond]))
    else do
      (_,rt) <- nonfailCondExpOf qf ftype args
      return rt

-- Returns the non-failure condition expression for a given operation
-- and its arguments (which are assumed to be variable indices).
-- All local variables are renamed by adding the `freshvar` index to them.
-- If the non-failure condition requires more arguments (due to a
-- higher-order call), fresh arguments are added which are also returned.
nonfailCondExpOf :: QName -> TypeExpr -> [(Int,TypeExpr)]
                 -> TransStateM ([(Int,TypeExpr)], SMT.Term)
nonfailCondExpOf qf ftype args = do
  nfconds <- lift $ gets $ nfConds . trInfo
  isError <- lift $ getOption optError
  maybe
    (predefs qf isError)
    (\fd -> let moreargs = funcArity fd - length args in
            if moreargs > 0
              then do
                -- eta-expand function call with fresh variables so that one
                -- can check non-fail conditions with a greater arity:
                let etatypes = argTypes (dropArgTypes (length args) ftype)
                fvars <- getFreshVarsForTypes (take moreargs etatypes)
                rt    <- applyFunc fd (args ++ fvars) >>= pred2SMT
                return (fvars,rt)
              else if moreargs < 0
                     then error $ "Operation '" ++ snd qf ++
                                  "': nonfail condition has too few arguments!"
                     else do rt <- applyFunc fd args >>= pred2SMT
                             return ([],rt) )
    (find (\fd -> decodeContractQName (funcName fd) == toNonFailQName qf)
          nfconds)
 where
  predefs qn isError | qn `elem` [pre "failed", pre "=:="] ||
                       (qn == pre "error" && isError)
                     = return ([], false)
                     | otherwise
                     = return ([], true)

-- Get for the types (given in the first argument) fresh typed variables.
getFreshVarsForTypes :: [TypeExpr] -> TransStateM [(VarIndex, TypeExpr)]
getFreshVarsForTypes types = do
  fv <- getFreshVarIndex
  let n     = length types
      vars  = take n [fv ..]
      tvars = zip vars types
  setFreshVarIndex (fv + n)
  addVarTypes tvars
  return tvars


-- Rename let-bound variables in a let expression.
renameLetVars :: [((VarIndex, TypeExpr), TAExpr)] -> TAExpr
              -> TransStateM ([((VarIndex, TypeExpr), TAExpr)], TAExpr)
renameLetVars bindings exp = do
  fv <- getFreshVarIndex
  let args = map (fst . fst) bindings
      minarg = minimum (0 : args)
      maxarg = maximum (0 : args)
      rnm i = if i `elem` args then i - minarg + fv else i
      nargs = map (\ ((v,t),_) -> (rnm v,t)) bindings
  setFreshVarIndex (fv + maxarg - minarg + 1)
  addVarTypes nargs
  return (map (\ ((v,t),be) -> ((rnm v,t), rnmAllVars rnm be)) bindings,
          rnmAllVars rnm exp)


-- Rename free variables introduced in an expression.
renameFreeVars :: [(VarIndex, TypeExpr)] -> TAExpr
               -> TransStateM ([(VarIndex, TypeExpr)], TAExpr)
renameFreeVars freevars exp = do
  fv <- getFreshVarIndex
  let args = map fst freevars
      minarg = minimum (0 : args)
      maxarg = maximum (0 : args)
      rnm i = if i `elem` args then i - minarg + fv else i
      nargs = map (\ (v,t) -> (rnm v,t)) freevars
  setFreshVarIndex (fv + maxarg - minarg + 1)
  addVarTypes nargs
  return (map (\ (v,t) -> (rnm v,t)) freevars, rnmAllVars rnm exp)


-- Rename argument variables of constructor pattern
renamePatternVars :: TABranchExpr -> TransStateM TABranchExpr
renamePatternVars (ABranch p e) = do
  if isConsPattern p
    then do fv <- getFreshVarIndex
            let args = map fst (patArgs p)
                minarg = minimum (0 : args)
                maxarg = maximum (0 : args)
                rnm i = if i `elem` args then i - minarg + fv else i
                nargs = map (\ (v,t) -> (rnm v,t)) (patArgs p)
            setFreshVarIndex (fv + maxarg - minarg + 1)
            addVarTypes nargs
            return $ ABranch (updPatArgs (map (\ (v,t) -> (rnm v,t))) p)
                             (rnmAllVars rnm e)
    else return $ ABranch p e

--- Tests whether the given branches of a case expressions
--- are a Boolean case distinction.
--- If yes, the expressions of the `False` and `True` branch
--- are returned.
testBoolCase :: [TABranchExpr] -> Maybe (TAExpr,TAExpr)
testBoolCase brs =
  if length brs /= 2 then Nothing
                     else case (brs!!0, brs!!1) of
    (ABranch (APattern _ (c1,_) _) e1, ABranch (APattern _ (c2,_) _) e2) ->
      if c1 == pre "False" && c2 == pre "True"  then Just (e1,e2) else
      if c1 == pre "True"  && c2 == pre "False" then Just (e2,e1) else Nothing
    _ -> Nothing
