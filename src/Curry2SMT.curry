-----------------------------------------------------------------------------
--- A tool to translate FlatCurry operations into SMT assertions.
---
--- @author  Michael Hanus
--- @version May 2021
---------------------------------------------------------------------------

module Curry2SMT where

import Data.List     ( intercalate, isPrefixOf, nub, union )
import Data.Maybe    ( catMaybes, fromJust, fromMaybe )
import Numeric       ( readHex )

-- Imports from dependencies:
import FlatCurry.Annotated.Goodies ( argTypes, resultType )
import FlatCurry.Types             ( showQName )
import Language.SMTLIB.Goodies
import qualified Language.SMTLIB.Types as SMT

-- Imports from package modules:
import ESMT
import FlatCurry.Typed.Read    ( getAllFunctions )
import FlatCurry.Typed.Goodies
import FlatCurry.Typed.Names
import FlatCurry.Typed.Types
import VerifierState

--- Translates a list of operations specified by their qualified name
--- (together with all operations on which these operation depend on)
--- into an SMT string that axiomatizes their semantics.
funcs2SMT :: [QName] -> VStateM [FunSigTerm]
funcs2SMT qns = do
  funs <- getAllFunctions [] (nub qns)
  return $ map fun2SMT funs

-- Translate a function declaration into a (possibly polymorphic)
-- SMT function declaration.
fun2SMT :: TAFuncDecl -> ([SMT.Ident],FunSig,SMT.Term)
fun2SMT (AFunc qn _ _ texp rule) =
  let fsig = FunSig (transOpName qn)
                    (map polytype2psort (argTypes texp))
                    (polytype2psort (resultType texp))
      srule = rule2SMT rule
      tpars = union (typeParamsOfFunSig fsig) (typeParamsOfTerm srule)
  in (tpars, fsig, srule)
 where
  rule2SMT (AExternal _ s) =
    (tcomb (transOpName qn) []) =% (tcomb ("External:" ++ s) [])
  rule2SMT (ARule _ vs exp) =
    SMT.Forall (map (\ (v,t) -> SMT.SV (var2SMT v) (polytype2psort t)) vs)
           (if ndExpr exp then exp2SMT (Just lhs) exp
                          else lhs =% (exp2SMT Nothing exp))
   where
    lhs = tcomb (transOpName qn) (map (tvar . fst) vs)


-- Translates a typed FlatCurry expression into an SMT expression.
-- If the first argument is an SMT expression, an equation between
-- this expression and the translated result expression is generated.
-- This is useful to axiomatize non-deterministic operations.
exp2SMT :: Maybe SMT.Term -> TAExpr -> SMT.Term
exp2SMT lhs exp = case exp of
  AVar _ i          -> makeRHS $ tvar i
  ALit _ l          -> makeRHS $ lit2SMT l
  AComb _ ct (qn,ftype) args ->
    -- TODO: reason about condition `not (null args)`
    makeRHS (SMT.TComb (cons2SMT (ct /= ConsCall || not (null args)) True qn ftype)
                   (map (exp2SMT Nothing) args))
  ACase _ _ e brs -> let be = exp2SMT Nothing e
                     in branches2SMT be brs
  ALet   _ bs e -> SMT.Let (map (\ ((v,_),be) -> (var2SMT v, exp2SMT Nothing be)) bs)
                       (exp2SMT lhs e)
  ATyped _ e _ -> exp2SMT lhs e
  AFree  _ fvs e -> SMT.Forall (map (\ (v,t) -> SMT.SV (var2SMT v) (polytype2psort t)) fvs)
                           (exp2SMT lhs e)
  AOr    _ e1 e2 -> tor [exp2SMT lhs e1, exp2SMT lhs e2]
 where
  makeRHS rhs = maybe rhs (\l -> l =% rhs) lhs

  branches2SMT _  [] = error "branches2SMT: empty branch list"
  branches2SMT be [ABranch p e] = branch2SMT be p e
  branches2SMT be (ABranch p e : brs@(_:_)) =
    tcomb "ite" [patternTest p be, --tEqu be (pat2smt p),
                 branch2SMT be p e,
                 branches2SMT be brs]

  branch2SMT _  (ALPattern _ _) e = exp2SMT lhs e
  branch2SMT be (APattern _ (qf,_) ps) e = case ps of
    [] -> exp2SMT lhs e
    _  -> SMT.Let (map (\ (s,v) -> (var2SMT v, tcomb s [be]))
                   (zip (selectors qf) (map fst ps)))
              (exp2SMT lhs e)

patternTest :: TAPattern -> SMT.Term -> SMT.Term
patternTest (ALPattern _ l)        be = be =% (lit2SMT l)
patternTest (APattern ty (qf,_) _) be = constructorTest True qf be ty

--- Translates a constructor name and a term into an SMT formula
--- implementing a test on the term for this constructor.
--- If the first argument is true, parametric sorts are used
--- (i.e., we translate a polymorphic function), otherwise
--- type variables are translated into the sort `TVar`.
constructorTest :: Bool -> QName -> SMT.Term -> TypeExpr -> SMT.Term
constructorTest withpoly qn be vartype
  | qn == pre "[]"
  = be =% (sortedConst "nil"
            ((if withpoly then polytype2psort else polytype2sort) vartype))
  | qn `elem` map pre ["[]","True","False","LT","EQ","GT","Nothing"]
  = be =% (tcomb (transOpName qn) [])
  | qn `elem` map pre ["Just","Left","Right"]
  = tcomb ("is-" ++ snd qn) [be]
  | otherwise
  = tcomb ("is-" ++ transOpName qn) [be]

--- Computes the SMT selector names for a given constructor.
selectors :: QName -> [String]
selectors qf | qf == ("Prelude",":")     = ["head","tail"]
             | qf == ("Prelude","Left")  = ["left"]
             | qf == ("Prelude","Right") = ["right"]
             | qf == ("Prelude","Just")  = ["just"]
             | otherwise = map (genSelName qf) [1..]

--- Translates a FlatCurry type expression into a corresponding SMT sort.
--- Polymorphic type variables are translated into the sort `TVar`.
--- The types `TVar` and `Func` are defined in the SMT prelude
--- which is always loaded.
polytype2sort :: TypeExpr -> SMT.Sort
polytype2sort = type2sort [] False False

--- Translates a FlatCurry type expression into a parametric SMT sort.
--- Thus, a polymorphic type variable `i` is translated into the sort `TVari`.
--- These type variables are later processed by the SMT translator.
polytype2psort :: TypeExpr -> SMT.Sort
polytype2psort = type2sort [] True False

--- Translates a FlatCurry type expression into a corresponding SMT sort.
--- If the first argument is null, then type variables are
--- translated into the sort `TVar`. If the second argument is true,
--- the type variable index is appended (`TVari`) in order to generate
--- a polymorphic sort (which will later be translated by the
--- SMT translator).
--- If the first argument is not null, we are in the translation
--- of the types of selector operations and the first argument
--- contains the currently defined data types. In this case, type variables
--- are translated into  `Ti`, but further nesting of the defined data types
--- are not allowed (since this is not supported by SMT).
--- The types `TVar` and `Func` are defined in the SMT prelude
--- which is always loaded.
type2sort :: [QName] -> Bool -> Bool -> TypeExpr -> SMT.Sort
type2sort tdcl poly _  (TVar i) =
  SMT.SComb (if null tdcl then "TVar" ++ (if poly then show i else "")
                      else 'T' : show i) []
type2sort tdcl poly _ (FuncType dom ran) =
  SMT.SComb "Func" (map (type2sort tdcl poly True) [dom,ran])
type2sort tdcl poly nested (TCons qc@(mn,tc) targs)
  | null tdcl
  = SMT.SComb (tcons2SMT qc) argtypes
  | otherwise -- we are in the selector definition of a datatype
  = if qc `elem` tdcl
      then if nested
             then error $ "Type '" ++ showQName qc ++
                          "': nested recursive types not supported by SMT!"
             else SMT.SComb (tcons2SMT qc) argtypes
                            -- TODO: check whether arguments
                            -- are directly recursive, otherwise emit error
      else SMT.SComb (tcons2SMT (mn,tc)) argtypes
 where
  argtypes = map (type2sort tdcl poly True) targs
type2sort _ _ _ (ForallType _ _) =
  error "Curry2SMT.type2SMT: cannot translate ForallType"


--- Translates a FlatCurry type constructor name into SMT.
tcons2SMT :: QName -> String
tcons2SMT (mn,tc)
 | "_Dict#" `isPrefixOf` tc
 = "Dict" -- since we do not yet consider class dictionaries...
 | mn == "Prelude" && take 3 tc == "(,,"
 = "Tuple" ++ show (length tc - 1)
 | mn == "Prelude"
 = maybe (encodeSpecialChars tc) id (lookup tc transPrimTCons)
 | otherwise
 = mn ++ "_" ++ encodeSpecialChars tc

----------------------------------------------------------------------------
--- Translates a type declaration into an SMT datatype declaration.
tdecl2SMT :: TypeDecl -> SMT.Command
tdecl2SMT (TypeSyn tc _ _ _) =
  error $ "Cannot translate type synonym '" ++ showQName tc ++ "' into SMT!"
tdecl2SMT (TypeNew tc _ _ _) =
  error $ "Cannot translate newtype '" ++ showQName tc ++ "' into SMT!"
tdecl2SMT (Type tc _ tvars consdecls) =
  SMT.DeclareDatatypes
   [(SMT.SortDecl (tcons2SMT tc) (length tvars),
     SMT.PT (map (\ (v,_) -> 'T' : show v) tvars) (map tconsdecl consdecls))]
 where
  tconsdecl (Cons qn _ _ texps) =
    let cname = transOpName qn
    in SMT.Cons cname (map (texp2sel qn) (zip [1..] texps))

  texp2sel cname (i,texp) = SMT.SV (genSelName cname i)
                              (type2sort [tc] False False texp)

--- Generates the name of the i-th selector for a given constructor.
genSelName :: QName -> Int -> String
genSelName qc@(mn,fn) i
 | mn == "Prelude" && take 3 fn == "(,,"
 = transOpName qc ++ "_" ++ show i
 | otherwise
 = "sel" ++ show i ++ '-' : transOpName qc

--- Translates a prelude type into an SMT datatype declaration,
--- if necessary.
preludeType2SMT :: String -> [SMT.Command]
preludeType2SMT tn
 | take 3 tn == "(,,"
 = let arity = length tn -1
   in [SMT.DeclareDatatypes
        [(SMT.SortDecl (tcons2SMT $ pre tn) arity,
          SMT.PT (map (\v -> 'T':show v) [1 .. arity])
             [SMT.Cons (transOpName $ pre tn) (map texp2sel [1 .. arity])])]]
 | otherwise
 = []
 where
  texp2sel i = SMT.SV (genSelName (pre tn) i) (SMT.SComb ('T' : show i) [])

---------------------------------------------------------------------------

--- Translates a qualifed name with given result type into an SMT identifier.
--- If the first argument is true and the result type is not a base type,
--- the type is attached via `(as ...)` to resolve overloading problems in SMT.
--- If the second argument is true, parametric sorts are used
--- (i.e., we translate a polymorphic function), otherwise
--- type variables are translated into the sort `TVar`.
cons2SMT :: Bool -> Bool -> QName -> TypeExpr -> SMT.QIdent
cons2SMT withas withpoly qf rtype =
  if withas && not (isBaseType rtype)
    then SMT.As (transOpName qf)
            ((if withpoly then polytype2psort else polytype2sort) rtype)
    else SMT.Id (transOpName qf)

--- Translates a pattern into an SMT expression.
pat2SMT :: TAPattern -> SMT.Term
pat2SMT (ALPattern _ l)    = lit2SMT l
pat2SMT (APattern ty (qf,_) ps)
  | qf == pre "[]" && null ps
  = sortedConst "nil" (polytype2sort ty)
  | otherwise
  = tcomb (transOpName qf) (map (tvar . fst) ps)

--- Translates a literal into an SMT expression.
lit2SMT :: Literal -> SMT.Term
lit2SMT (Intc i)   = tint i
lit2SMT (Floatc f) = tfloat f
lit2SMT (Charc c)  = tchar c

--- Translates a qualified FlatCurry name into an SMT string.
transOpName :: QName -> String
transOpName (mn,fn)
 | mn=="Prelude" = fromMaybe tname (lookup fn (transPrimCons ++ preludePrimOps))
 | otherwise     = tname
 where
  tname = mn ++ "_" ++ encodeSpecialChars fn

--- Encode special characters in strings
encodeSpecialChars :: String -> String
encodeSpecialChars = concatMap encChar
 where
  encChar c | c `elem` "#$%[]()!,"
            = let oc = ord c
              in ['%', int2hex (oc `div` 16), int2hex(oc `mod` 16)]
            | otherwise = [c]

  int2hex i = if i<10 then chr (ord '0' + i)
                      else chr (ord 'A' + i - 10)

--- Translates urlencoded string into equivalent ASCII string.
decodeSpecialChars :: String -> String
decodeSpecialChars [] = []
decodeSpecialChars (c:cs)
  | c == '%'  = let n = case readHex (take 2 cs) of
                          [(h,"")] -> h
                          _        -> 0
                in chr n : decodeSpecialChars (drop 2 cs)
  | otherwise = c : decodeSpecialChars cs


--- Translates a (translated) SMT string back into qualified FlatCurry name.
--- Returns Nothing if it was not a qualified name.
untransOpName :: String -> Maybe QName
untransOpName s
 | "is-" `isPrefixOf` s
 = Nothing -- selectors are not a qualified name
 | otherwise
 = let (mn,ufn) = break (=='_') s
   in if null ufn
        then Nothing
        else Just (mn, decodeSpecialChars (tail ufn))

----------------------------------------------------------------------------
