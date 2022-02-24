module ContractProver
  ( addPreConditions, verifyPostConditions, verifyPreConditions
  ) where

import Control.Monad               ( unless )
import Contract.Names
import Control.Monad.IO.Class      ( liftIO )
import Control.Monad.Trans.Class   ( lift )
import Control.Monad.Trans.State   ( evalStateT, gets, put )
import Data.List                   ( elemIndex, find, init, intercalate
                                   , maximum, minimum )
import Data.Maybe                  ( isJust )

import FlatCurry.Annotated.Goodies
import FlatCurry.Annotated.Types
import FlatCurry.Show              ( showCurryType )
import FlatCurry.Types             ( showQName )
import Language.SMTLIB.Goodies
import qualified Language.SMTLIB.Types as SMT

import CheckSMT
import Common
import Curry2SMT
import FlatCurry.Typed.Build
import FlatCurry.Typed.Read
import FlatCurry.Typed.Simplify
import FlatCurry.Typed.Types
import ToolOptions
import TransState
import VerifierState

------------------------------------------------------------------------
-- Try to verify postconditions: If an operation `f` has a postcondition,
-- a proof for the validity of the postcondition is extracted.
-- If the proof is not successful, a postcondition check is added to `f`.
verifyPostConditions :: TAProg -> VStateM TAProg
verifyPostConditions prog = do
  postconds <- gets $ postConds . trInfo
  -- Operations with postcondition checks:
  let fdecls = progFuncs prog
  newfuns <- provePostConds postconds fdecls
  return $ updProgFuncs (const newfuns) prog
 where
  provePostConds []           fdecls = return fdecls
  provePostConds (pof : pofs) fdecls =
    provePostCondition pof fdecls >>= provePostConds pofs

provePostCondition :: TAFuncDecl -> [TAFuncDecl] -> VStateM [TAFuncDecl]
provePostCondition postfun allfuns = do
  maybe (do liftIO $ putStrLn $ "Postcondition: " ++ pcname ++ "\n" ++
                                "Operation of this postcondition not found!"
            return allfuns)
        (\checkfun -> evalStateT (provePC (simpFuncDecl checkfun))
                                 emptyTransState)
        (find (\fd -> toPostCondName (snd (funcName fd)) ==
                      decodeContractName pcname)
              allfuns)
 where
  pcname = snd (funcName postfun)

  provePC :: TAFuncDecl -> TransStateM [TAFuncDecl]
  provePC checkfun = do
    let (postmn,postfn) = funcName postfun
        mainfunc        = snd (funcName checkfun)
        orgqn           = (postmn, reverse (drop 5 (reverse postfn)))
        farity = funcArity checkfun
        ftype  = funcType checkfun
        targsr = zip [1..] (argTypes ftype ++ [resultType ftype])
    bodyformula     <- extractPostConditionProofObligation [1 .. farity]
                         (farity+1) (funcName checkfun) (funcRule checkfun)
    precondformula  <- preCondExpOf orgqn (init targsr)
    postcondformula <- applyFunc postfun targsr >>= pred2SMT
    let title = "verify postcondition of '" ++ mainfunc ++ "'..."
    lift $ printWhenIntermediate $ "Trying to " ++ title
    mbsmt <- checkPostCon ("SMT script to " ++ title)
                          (tand [precondformula, bodyformula])
                          true postcondformula
    maybe (lift $ do
             printWhenStatus $ mainfunc ++ ": POSTCOND CHECK ADDED"
             addPostCondToStats mainfunc False
             return $ map (addPostConditionTo (funcName postfun)) allfuns)
          (\proof -> lift $ do
             printWhenStatus $ mainfunc ++ ": POSTCONDITION VERIFIED"
             whenOption optStoreProof $ liftIO $
               writeFile ("PROOF_" ++ showQNameNoDots orgqn ++ "_" ++
                          "SatisfiesPostCondition.smt") proof
             addPostCondToStats mainfunc True
             return allfuns)
          mbsmt

-- If the function declaration is the declaration of the given function name,
-- decorate it with a postcondition check.
addPostConditionTo :: QName -> TAFuncDecl -> TAFuncDecl
addPostConditionTo pfname fdecl = let fn = funcName fdecl in
  if toPostCondQName fn == pfname
    then updFuncBody (const (addPostConditionCheck fn (funcRule fdecl))) fdecl
    else fdecl

-- Adds a postcondition check to a program rule of a given operation.
addPostConditionCheck :: QName -> TARule -> TAExpr
addPostConditionCheck _ (AExternal _ _) =
  error $ "Trying to add postcondition to external function!"
addPostConditionCheck qf@(mn,fn) (ARule ty lhs rhs) = --ALit boolType (Intc 42)
  AComb ty FuncCall
    ((mn, "checkPostCond_" ++ type2ID tt ++ "_" ++ type2ID (annExpr rhs)),
     FuncType ty (FuncType (FuncType ty boolType)
                           (FuncType stringType (FuncType tt ty))))
    [ rhs
    , AComb boolType (FuncPartCall 1) (toPostCondQName qf, ty) args
    , string2TAFCY fn
    , tupleExpr args
    ]
 where
  args = map (\ (i,t) -> AVar t i) lhs
  tt = tupleType (map annExpr args)

extractPostConditionProofObligation :: [Int] -> Int -> QName -> TARule
                                    -> TransStateM SMT.Term
extractPostConditionProofObligation _ _ _ (AExternal _ s) =
  return $ tcomb ("External: " ++ s) []
extractPostConditionProofObligation args resvar fname
                                    (ARule ty orgargs orgexp) = do
  let exp    = rnmAllVars renameRuleVar orgexp
      rtype  = resType (length orgargs) (stripForall ty)
  put $ makeTransState
            (maximum (resvar : allVars exp) + 1)
            ((resvar, rtype, Just (fname, 0, 1))
              : map (\(i,x,y) -> (x, y, Just (fname, i, 1)))
                (zip3 [1..] args $ map snd orgargs))
  binding2SMT True (resvar,exp)
 where
  maxArgResult = maximum (resvar : args)
  renameRuleVar r = maybe (r + maxArgResult + 1)
                          (args!!)
                          (elemIndex r (map fst orgargs))

  resType n te =
    if n==0
      then te
      else case te of
             FuncType _ rt -> resType (n-1) rt
             _             -> error $ "Internal errror: resType: " ++ show te

---------------------------------------------------------------------------
-- Try to verify preconditions: If an operation `f` occurring in some
-- right-hand side has a precondition, a proof for the validity of
-- this precondition is extracted.
-- If the proof is not successful, a precondition check is added to this call.
verifyPreConditions :: TAProg -> VStateM TAProg
verifyPreConditions prog = do
  newfuns  <- mapM provePreCondition $ progFuncs prog
  return (updProgFuncs (const newfuns) prog)

provePreCondition :: TAFuncDecl -> VStateM TAFuncDecl
provePreCondition fdecl = do
  printWhenIntermediate $
    "Operation to be checked: " ++ snd (funcName fdecl)
  newrule <- optPreConditionInRule (funcName fdecl) (funcRule fdecl)
  return (updFuncRule (const newrule) fdecl)

optPreConditionInRule :: QName -> TARule -> VStateM TARule
optPreConditionInRule _ rl@(AExternal _ _)            = return rl
optPreConditionInRule qn@(_,fn) (ARule rty rargs rhs) = do
  let targs = zip [1..] (map snd rargs)
      st = makeTransState
            (maximum (0 : map fst rargs ++ allVars rhs) + 1)
            (map (\(i,(x,y)) -> (x, y, Just (qn, i, 0))) (zip [1..] rargs))
  (flip evalStateT) st $ do
    -- compute precondition of operation:
    precondformula <- preCondExpOf qn targs
    setAssertion precondformula
    newrhs <- optPreCondInExp rhs
    return $ ARule rty rargs newrhs
 where
  optPreCondInExp exp = case exp of
    AComb ty ct (qf,tys) args -> do
      precond  <- getAssertion
      nargs    <- mapM optPreCondInExp args
      preconds <- lift $ gets $ preConds . trInfo
      if toPreCondQName qf `elem` map funcName preconds
        then do
          lift $ printWhenIntermediate $ "Checking call to " ++ snd qf
          (bs,_)   <- normalizeArgs nargs
          setNameOfVars qf $ map fst bs
          bindexps <- mapM (binding2SMT True) bs
          precondcall <- preCondExpOf qf
                           (zip (map fst bs) (map annExpr args))
          -- TODO: select from 'bindexps' only demanded argument positions
          let title = "SMT script to verify precondition of '" ++ snd qf ++
                      "' in function '" ++ fn ++ "'"
          valid <- checkPreCon title precond (tand bindexps) precondcall
                     fn (map fst rargs)
          if valid == Just True
            then lift $ do
              printWhenStatus $
                fn ++ ": PRECONDITION OF '" ++ snd qf ++ "': VERIFIED"
              addPreCondToStats (snd qf ++ "(" ++ fn ++ ")") True
              return $ AComb ty ct (toNoCheckQName qf, tys) nargs
            else lift $ do
              printWhenStatus $
                fn ++ ": PRECOND CHECK ADDED TO '" ++ snd qf ++ "'"
              addPreCondToStats (snd qf ++ "("++ fn ++ ")") False
              return $ AComb ty ct (qf,tys) nargs
        else return $ AComb ty ct (qf,tys) nargs
    ACase ty ct e brs -> do
      ne <- optPreCondInExp e
      freshvar <- getFreshVar
      be <- binding2SMT True (freshvar,ne)
      addToAssertion be
      addVarTypes [ (freshvar, annExpr ne) ]
      nbrs <- mapM (optPreCondInBranch freshvar) brs
      return $ ACase ty ct ne nbrs
    AOr ty e1 e2 -> do
      ne1 <- optPreCondInExp e1
      ne2 <- optPreCondInExp e2
      return $ AOr ty ne1 ne2
    ALet ty bs e -> do
      nes <- mapM optPreCondInExp (map snd bs)
      ne  <- optPreCondInExp e
      return $ ALet ty (zip (map fst bs) nes) ne
    AFree ty fvs e -> do
      ne <- optPreCondInExp e
      return $ AFree ty fvs ne
    ATyped ty e et -> do
      ne <- optPreCondInExp e
      return $ ATyped ty ne et
    _ -> return exp

  optPreCondInBranch dvar branch = do
    ABranch p e <- renamePatternVars branch
    addToAssertion (tvar dvar =% pat2SMT p)
    ne <- optPreCondInExp e
    return (ABranch p ne)

-- Rename argument variables of constructor pattern
renamePatternVars :: TABranchExpr -> TransStateM TABranchExpr
renamePatternVars (ABranch p e) =
  if isConsPattern p
    then do
      fv <- getFreshVarIndex
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

---------------------------------------------------------------------------
-- Add (non-trivial) preconditions:
-- If an operation `f` has some precondition `f'pre`,
-- replace the rule `f xs = rhs` by the following rules:
--
--     f xs = checkPreCond (f'NOCHECK xs) (f'pre xs) "f" xs
--     f'NOCHECK xs = rhs
addPreConditions :: TAProg -> VStateM TAProg
addPreConditions prog = do
  newfuns  <- mapM addPreCondition (progFuncs prog)
  return $ updProgFuncs (const (concat newfuns)) prog
 where
  addPreCondition fdecl@(AFunc qf ar vis fty rule) = do
    preconds <- gets $ preConds . trInfo
    return $
      if toPreCondQName qf `elem` map funcName preconds
        then let newrule = checkPreCondRule qf rule
             in [updFuncRule (const newrule) fdecl,
                 AFunc (toNoCheckQName qf) ar vis fty rule]
        else [fdecl]

  checkPreCondRule :: QName -> TARule -> TARule
  checkPreCondRule qn (ARule rty rargs _) =
    ARule rty rargs (addPreConditionCheck rty FuncCall qn rty
                       (map (\ (v,t) -> AVar t v) rargs))
  checkPreCondRule qn (AExternal _ _) = error $
    "addPreConditions: cannot add precondition to external operation '" ++
    snd qn ++ "'!"

-- Adds a precondition check to a original call of the form
-- `AComb ty ct (qf,tys) args`.
addPreConditionCheck :: TypeExpr -> CombType -> QName -> TypeExpr
                     -> [TAExpr] -> TAExpr
addPreConditionCheck ty ct qf@(mn,fn) tys args =
  AComb ty FuncCall
    ((mn, "checkPreCond_" ++ type2ID tt),
     FuncType ty (FuncType boolType (FuncType stringType (FuncType tt ty))))
    [ AComb ty ct (toNoCheckQName qf,tys) args
    , AComb boolType ct (toPreCondQName qf, pctype) args
    , string2TAFCY fn
    , tupleExpr args
    ]
 where
  argtypes = map annExpr args
  tt       = tupleType argtypes
  pctype   = foldr FuncType boolType argtypes

-- Translate a type expression into an identifier which is the suffix
-- of `checkPreCond` which is a type-specialized instance.
type2ID :: TypeExpr -> String
type2ID te = case te of
  TCons (mn,tc) tes | mn == "Prelude" && null tes
    -> intercalate "_" (tc2ID tc : map type2ID tes)
  _ -> "Any"
 where
  tc2ID tc | tc == "[]" = "List"
           | tc == "()" = "Unit"
           | otherwise  = tc

---------------------------------------------------------------------------
-- Auxiliaries:

--- Transform a qualified name into a name of the corresponding function
--- without precondition checking by adding the suffix "'NOCHECK".
toNoCheckQName :: (String,String) -> (String,String)
toNoCheckQName (mn,fn) = (mn, fn ++ "'NOCHECK")

-- Shows a qualified name by replacing all dots by underscores.
showQNameNoDots :: QName -> String
showQNameNoDots = map (\c -> if c=='.' then '_' else c) . showQName

---------------------------------------------------------------------------
