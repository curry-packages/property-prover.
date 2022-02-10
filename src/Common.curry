module Common where

import Control.Monad.Trans.Class         ( lift )
import Control.Monad.Trans.State         ( gets )
import Data.List                         ( elemIndex, find, maximum )

import Contract.Names
import FlatCurry.Annotated.Goodies
import FlatCurry.TypeAnnotated.TypeSubst ( substRule )
import Language.SMTLIB.Goodies
import qualified Language.SMTLIB.Types as SMT

import Curry2SMT
import ESMT
import FlatCurry.Typed.Goodies
import FlatCurry.Typed.Names
import FlatCurry.Typed.Simplify
import FlatCurry.Typed.Types
import ToolOptions
import TransState
import VerifierState

---------------------------------------------------------------------------
-- Translates a FlatCurry expression to a Boolean formula representing
-- the binding of a variable (represented by its index in the first
-- component) to the translated expression (second component).
-- The translated expression is normalized when necessary.
-- For this purpose, a "fresh variable index" is passed as a state.
-- Moreover, the returned state contains also the types of all fresh variables.
-- If the first argument is `False`, the expression is not strictly demanded,
-- i.e., possible contracts of it (if it is a function call) are ignored.
binding2SMT :: Bool -> (Int,TAExpr) -> TransStateM SMT.Term
binding2SMT demanded (resvar,exp) =
 case simpExpr exp of
  AVar _ i -> return $ if resvar==i then true
                                    else tvar resvar =% tvar i
  ALit _ l -> return (tvar resvar =% lit2SMT l)
  AComb rtype ct (qf,_) args -> do
    (bs,nargs) <- normalizeArgs args
    isStrict   <- lift $ getOption optStrict
    -- TODO: select from 'bindexps' only demanded argument positions
    bindexps <- mapM (binding2SMT $ isPrimOp qf || isStrict) bs
    comb2bool qf rtype ct nargs bs bindexps
  ALet _ bs e -> do
    bindexps <- mapM (binding2SMT False)
                    (map (\ ((i,_),ae) -> (i,ae)) bs)
    bexp <- binding2SMT demanded (resvar,e)
    return (tand (bindexps ++ [bexp]))
  AOr _ e1 e2  -> do
    bexp1 <- binding2SMT demanded (resvar,e1)
    bexp2 <- binding2SMT demanded (resvar,e2)
    return (tor [bexp1, bexp2])
  ACase _ _ e brs   -> do
    freshvar <- getFreshVar
    addVarTypes [(freshvar, annExpr e)]
    argbexp <- binding2SMT demanded (freshvar,e)
    bbrs    <- mapM branch2bool (map (\b->(freshvar,b)) brs)
    return (tand [argbexp, tor bbrs])
  ATyped _ e _ -> binding2SMT demanded (resvar,e)
  AFree _ _ _ -> error "Free variables not yet supported!"
 where
   comb2bool qf rtype ct nargs bs bindexps
    | qf == pre "otherwise"
      -- specific handling for the moment since the front end inserts it
      -- as the last alternative of guarded rules...
    = return (tvar resvar =% true)
    | ct == ConsCall
    = return (tand (bindexps ++
                    [tvar resvar =%
                             (SMT.TComb (cons2SMT (null nargs) False qf rtype)
                                    (map arg2bool nargs))]))
    | qf == pre "apply"
    = -- cannot translate h.o. apply: ignore it
      return true
    | isPrimOp qf
    = return (tand (bindexps ++
                    [tvar resvar =%
                             (SMT.TComb (cons2SMT True False qf rtype)
                                    (map arg2bool nargs))]))
    | otherwise -- non-primitive operation: add contract only if demanded
    = do let targs = zip (map fst bs) (map annExpr nargs)
         precond  <- preCondExpOf qf targs
         postcond <- postCondExpOf qf (targs ++ [(resvar,rtype)])
         isCon    <- lift $ getOption optConFail
         return (tand (bindexps ++
                       if demanded && isCon
                         then [precond,postcond]
                         else []))

   branch2bool (cvar, ABranch p e) = do
     branchbexp <- binding2SMT demanded (resvar,e)
     addVarTypes patvars
     return (tand [ tvar cvar =% pat2SMT p, branchbexp])
    where
     patvars = if isConsPattern p
                 then patArgs p
                 else []

   arg2bool e = case e of AVar _ i -> tvar i
                          ALit _ l -> lit2SMT l
                          _ -> error $ "Not normalized: " ++ show e

---------------------------------------------------------------------------
-- Returns the precondition expression for a given operation
-- and its arguments (which are assumed to be variable indices).
-- Rename all local variables by adding the `freshvar` index to them.
preCondExpOf :: QName -> [(Int,TypeExpr)] -> TransStateM SMT.Term
preCondExpOf qf args = do
  preconds <- lift $ gets $ preConds . trInfo
  maybe (return true)
        (\fd -> applyFunc fd args >>= pred2SMT)
        (find (\fd -> decodeContractQName (funcName fd)
                        == toPreCondQName (fromNoCheckQName qf)) preconds)

-- Returns the postcondition expression for a given operation
-- and its arguments (which are assumed to be variable indices).
-- Rename all local variables by adding `freshvar` to them and
-- return the new freshvar value.
postCondExpOf :: QName -> [(Int,TypeExpr)]
              -> TransStateM SMT.Term
postCondExpOf qf args = do
  postconds <- lift $ gets $ postConds . trInfo
  maybe (return true)
        (\fd -> applyFunc fd args >>= pred2SMT)
        (find (\fd -> decodeContractQName (funcName fd)
                        == toPostCondQName (fromNoCheckQName qf)) postconds)

-- Drops a possible "'NOCHECK" suffix from a qualified name.
fromNoCheckQName :: (String,String) -> (String,String)
fromNoCheckQName (mn,fn) =
  (mn, let rf = reverse fn
       in reverse (drop (if take 8 rf == "KCEHCON'" then 8 else 0) rf))

---------------------------------------------------------------------------
-- Applies a function declaration on a list of arguments,
-- which are assumed to be variable indices, and returns
-- the renamed body of the function declaration.
-- All local variables are renamed by adding `freshvar` to them.
-- Also the new fresh variable index is returned.
applyFunc :: TAFuncDecl -> [(Int,TypeExpr)] -> TransStateM TAExpr
applyFunc fdecl targs = do
  fv <- getFreshVarIndex
  let tsub = maybe (error $ "applyFunc: types\n" ++
                            show (argTypes (funcType fdecl)) ++ "\n" ++
                            show (map snd targs) ++ "\ndo not match!")
                   id
                   (matchTypes (argTypes (funcType fdecl)) (map snd targs))
      (ARule _ orgargs orgexp) = substRule tsub (funcRule fdecl)
      exp = rnmAllVars (renameRuleVar fv orgargs) orgexp
  setFreshVarIndex (max fv (maximum (0 : args ++ allVars exp) + 1))
  return $ simpExpr $ applyArgs exp (drop (length orgargs) args)
 where
  args = map fst targs
  -- renaming function for variables in original rule:
  renameRuleVar fv orgargs r = maybe (r + fv)
                                     (args!!)
                                     (elemIndex r (map fst orgargs))

  applyArgs e [] = e
  applyArgs e (v:vs) =
    -- eta-expansion
    let et@(FuncType vt rt) = annExpr e
        e_v = AComb rt FuncCall (pre "apply", FuncType et vt) [e, AVar vt v]
    in applyArgs e_v vs

---------------------------------------------------------------------------
-- Translates a Boolean FlatCurry expression into a Boolean formula.
-- Calls to user-defined functions are replaced by the first argument
-- (which might be true or false).
pred2SMT :: TAExpr -> TransStateM SMT.Term
pred2SMT exp = case exp of
  AVar  _ i                  -> return (tvar i)
  ALit  _ l                  -> return (lit2SMT l)
  AComb _ ct (qf,ftype) args -> comb2bool qf ftype ct (length args) args
  _                          -> return (tcomb (show exp) []) -- TODO!
 where
  comb2bool qf ftype ct ar args
    | qf == pre "[]" && ar == 0
    = return (sortedConst "nil" (polytype2sort (annExpr exp)))
    | qf == pre "not" && ar == 1
    = do barg <- pred2SMT (head args)
         return (tnot barg)
    | qf == pre "null" && ar == 1
    = do let arg = head args
         barg    <- pred2SMT arg
         typeOfVar arg >>= return . (barg =%) . maybe (tcomb "nil" [])
           (sortedConst "nil" . polytype2sort)
    | qf == pre "apply"
    = do -- cannot translate h.o. apply: replace it by new variable
         fvar <- getFreshVar
         addVarTypes [(fvar,annExpr exp)]
         return (tvar fvar)
    | qf == pre "/="
    = do be <- comb2bool (pre "==") ftype ct ar args
         return (tnot be)
    | otherwise
    = do bargs <- mapM pred2SMT args
         return (SMT.TComb (cons2SMT (ct /= ConsCall || not (null bargs))
                                 False qf ftype)
                       bargs)

  typeOfVar e =
    case e of
      AVar _ i -> getVarTypes >>= return . lookup i . map (\(x,y,_) -> (x,y))
      _        -> return $ Just $ annExpr e
                    -- might not be correct due to applyFunc!

---------------------------------------------------------------------------
normalizeArgs :: [TAExpr] -> TransStateM ([(Int,TAExpr)],[TAExpr])
normalizeArgs [] = return ([],[])
normalizeArgs (e:es) = case e of
  AVar _ i -> do (bs,nes) <- normalizeArgs es
                 return ((i,e):bs, e:nes)
  _        -> do fvar <- getFreshVar
                 addVarTypes [(fvar,annExpr e)]
                 (bs,nes) <- normalizeArgs es
                 return ((fvar,e):bs, AVar (annExpr e) fvar : nes)
