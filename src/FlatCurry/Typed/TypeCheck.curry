-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--- This module provides functions to check for typed flat curry programs and 
--- expressions type-sanity.
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
module FlatCurry.Typed.TypeCheck
  ( checkProgSanity
  , isSaneProg
  , typeClashes
  ) where

import           Control.Monad                        ( when )
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.State
import           FlatCurry.Annotated.Goodies
  ( annExpr, annPattern, domain, funcRule, progName, range, unAnnFuncDecl )
import           FlatCurry.ShowIntMod
  ( showFuncDeclAsFlatCurry )
import           FlatCurry.TypeAnnotated.Files
  ( readTypeAnnotatedFlatCurry )
import           FlatCurry.Typed.FunctionSubstitution ( makeTE )
import           FlatCurry.Typed.Goodies
  ( dropArgTypes, stripForall )
import           FlatCurry.Typed.Types

--- read a Typed Flat Curry program and test it for type-sanity
--- @param progname: Name of program that is supposed to 
---                  be tested for type-sanity
--- @param output: show output during check
checkProgSanity :: String -> Bool -> IO ()
checkProgSanity progname output = do
  putStrLn "beginning sanity check"
  tprog <- readTypeAnnotatedFlatCurry progname
  sanity <- isSaneProg tprog output
  putStrLn "Done with sanity check"
  putStrLn (if sanity
              then "The Program is type-sane"
              else "The Program is not type-sane!")

--- is an annotated flat curry program type-sane?
isSaneProg :: TAProg -> Bool -> IO Bool
isSaneProg prog output = if progName prog == "Prelude" then return True else do
  sanity <- typeClashes prog output
  return $ null sanity

--- give all expressions in a program that are not type-sane
typeClashes :: TAProg -> Bool -> IO [(TAExpr, String)]
typeClashes (AProg _ _ _ funcs _) output = typeSane output funcs

--- give all expressions in a list of function declarations
--- that are not type-sane
typeSane :: Bool -> [TAFuncDecl] -> IO [(TAExpr, String)]
typeSane output funcs = do
  res <- mapM (funcSanity output) funcs
  return (concat res)

--- give all expressions in a function declaration that are
--- not type-sane
funcSanity :: Bool -> TAFuncDecl -> IO [(TAExpr, String)]
funcSanity output f@(AFunc q n _ _ _) = do
  sanity <- ruleSanity (funcRule f) n q output
  when (output && not (null sanity))
    (putStrLn (showFuncDeclAsFlatCurry (unAnnFuncDecl f)) >> print f)
  return sanity

--- give all expressions in a rule body that are not type-sane
ruleSanity :: TARule -> Arity -> QName -> Bool -> IO [(TAExpr, String)]
ruleSanity rule n qn output = case rule of
  ARule a vars expr -> do
    res <- runStateT (saneExpr expr output)
      (Sanef expr vars (dropArgTypes n (stripForall a)) qn)
    return (fst res)
  AExternal _ _     -> return []

--saneExpr' :: Bool -> StateT Sanef IO ([(TAExpr, String)])
--saneExpr' output = do 
--   state <- get
--   let expr = stateExpr state
--   saneExpr expr output
-- give all expressions in an expression that are not type-sane
saneExpr :: TAExpr -> Bool -> StateT Sanef IO [(TAExpr, String)]
saneExpr expr output = case expr of
  AVar _ _      -> saneVar expr output
  ALit _ _      -> saneLit expr output
  AComb _ _ _ _ -> saneComb expr output
  ALet _ _ _    -> saneLet expr output
  AFree _ _ _   -> saneFree expr output
  AOr _ _ _     -> saneOr expr output
  ACase _ _ _ _ -> saneCase expr output
  ATyped _ _ _  -> saneTyped expr output

-- case expression type-sanity
saneCase :: TAExpr -> Bool -> StateT Sanef IO [(TAExpr, String)]
saneCase ca output = case ca of
  ACase a _ ex branches -> do
    state <- get
    let cty = currentType state
        qn  = fName state
    res <- do
      if a == cty then return [] else do
        let out = show qn
              ++ " is not type sane!. "
              ++ "Case-Expr Type "
              ++ show a
              ++ " does not"
              ++ " match expected type "
              ++ show cty
        lift $ when output $ putStrLn $ out
        return [(ca, out)]
    res2 <- mapM (saneBranch ex output) branches
    return (concat res2 ++ res)
  _                     -> error "SanityCheck.saneCase: no ACase"

--branch expression type-sanity
saneBranch
  :: TAExpr -> Bool -> TABranchExpr -> StateT Sanef IO [(TAExpr, String)]
saneBranch cex output (ABranch p ex) = do
  state <- get
  res2 <- sanePattern p
  res <- saneExpr ex output
  let qn = fName state
      pt = annPattern p
      ct = annExpr cex
  put state
  res1 <- do
    if pt == ct then return [] else do
      let out = show qn
            ++ " is not type sane!. "
            ++ "Pattern type "
            ++ show pt
            ++ " does not"
            ++ " match expected type "
            ++ show ct
      lift $ when output $ putStrLn out
      return [(cex, out)]
  return (res ++ res1 ++ res2)

sanePattern :: TAPattern -> StateT Sanef IO [(TAExpr, String)]
sanePattern p = case p of
  APattern _ _ vars -> do
    state <- get
    let globals = globalVars state
    put state { globalVars = globals ++ vars }
    return []
  ALPattern _ _     -> return []

-- let expression type-sanity
-- ALet a [((n,d), AExpr e)] (AExpr f)
-- 1. e = d
-- 2. f = a
-- 3. everywhere we find (AVar g n) in f, g = d must hold for (n,d)
-- 4. same goes for global vars
saneLet :: TAExpr -> Bool -> StateT Sanef IO [(TAExpr, String)]
saneLet l output = case l of
  ALet a lets expr -> do
    state <- get
    let vars = globalVars state
        qn   = fName state
        exa  = annExpr expr
    res1 <- do
      if exa == a then return [] else do
        let out = show qn
              ++ " is not type sane!. "
              ++ "Expr type "
              ++ show exa
              ++ " does not"
              ++ " match expected type "
              ++ show a
        lift $ when output $ putStrLn out
        return [(l, out)]
    letres <- mapM (saneLets output) lets
    put state { globalVars = vars ++ (fst (unzip lets)) }
    res <- saneExpr expr output
    return (res1 ++ res ++ concat letres)
  _                -> error "SanityCheck.saneLet: no ALet"

-- let-bound expression type-sanity
-- for every let expressin ((i,d), Expr e), e == d must hold
saneLets :: Bool
         -> ((VarIndex, TypeExpr), TAExpr)
         -> StateT Sanef IO [(TAExpr, String)]
saneLets output ((_, d), ex) = do
  state <- get
  let qn = fName state
      a  = annExpr ex
  if d == a then return [] else do
    let out = show qn
          ++ " is not type sane!. "
          ++ " Let-bound expr type"
          ++ show a
          ++ " does not"
          ++ " match expected type "
          ++ show d
    lift $ when output $ putStrLn out
    return [(ex, out)]

saneFree :: TAExpr -> Bool -> StateT Sanef IO [(TAExpr, String)]
saneFree f output = case f of
  AFree a vars expr -> do
    state <- get
    let ty = currentType state
        qn = fName state
    res <- do
      let out = show qn
            ++ " is not type sane!. "
            ++ "Free expr type "
            ++ show a
            ++ " does not"
            ++ " match expected type "
            ++ show ty
      if a == ty then return [] else do
        lift $ when output $ putStrLn out
        return [(f, out)]
    let globals = globalVars state
    put state { globalVars = vars ++ globals }
    res2 <- saneExpr expr output
    return (res ++ res2)
  _                 -> error "SanityCheck.saneFree: no AFree"

-- or expression type-sanity
saneOr :: TAExpr -> Bool -> StateT Sanef IO [(TAExpr, String)]
saneOr or output = case or of
  AOr a o1 o2 -> do
    state <- get
    let ty = currentType state
        qn = fName state
    res <- do
      let out = show qn
            ++ " is not type sane!. "
            ++ "Or Expr type "
            ++ show a
            ++ " does not"
            ++ " match expected type "
            ++ show ty
      if a == ty then return [] else do
        lift $ when output $ putStrLn out
        return [(or, out)]
    res1 <- saneExpr o1 output
    res2 <- saneExpr o2 output
    return (res ++ res1 ++ res2)
  _           -> error "SanityCheck.saneOr: no AOr"

-- comb expression type-sanity
-- AComb a ct (QName, b) [AExpr cn]
-- 1. b = FuncType c1 ... FuncType cn a
saneComb :: TAExpr -> Bool -> StateT Sanef IO [(TAExpr, String)]
saneComb ex output = case ex of
  AComb a _ (_, b) exs -> do
    state <- get
    let cty = currentType state
        qn  = fName state
    if a == cty then do
      let ty = makeTE exs a
      rest <- saneCombArguments exs ty output
      if ty == b then return rest else do
        let out = show qn
              ++ " is not type sane!. "
              ++ "Comb-expr type "
              ++ show b
              ++ " does not"
              ++ " match expected type "
              ++ show ty
        lift $ when output $ putStrLn out
        return ((ex, out) : rest) else do
      let out = show qn
            ++ " is not type sane!. "
            ++ "Expression type "
            ++ show a
            ++ " does not"
            ++ " match expected type "
            ++ show cty
      lift $ when output $ putStrLn out
      return [(ex, out)]
  _                    -> error "SanityCheck.saneComb: no AComb"

-- comb expressions arguments type-sanity
saneCombArguments
  :: [TAExpr] -> TypeExpr -> Bool -> StateT Sanef IO [(TAExpr, String)]
saneCombArguments args ty output = case args of
  []        -> return []
  (e : exs) -> do
    state <- get
    put state { currentType = domain ty }
    res <- saneExpr e output
    put state
    res2 <- saneCombArguments exs (range ty) output
    return (res ++ res2)

-- variable expression type-sanity
saneVar :: TAExpr -> Bool -> StateT Sanef IO [(TAExpr, String)]
saneVar v output = case v of
  AVar a i -> do
    state <- get
    let globals = globalVars state
        qn      = fName state
    case findgVar globals i of
      Just d  -> do
        if d == a then return [] else do
          let out = show qn
                ++ " is not type-sane."
                ++ " Variable type "
                ++ show a
                ++ " does not match "
                ++ show d
          lift $ when output $ putStrLn out
          return [(v, out)]
      Nothing -> do
        let out = show qn
              ++ " is not type-sane."
              ++ " Could not find variable "
              ++ show i
              ++ " in global vars"
        lift $ when output $ putStrLn out
        return [(v, out)]
  _        -> error "SanityCheck.saneVar: no AVar"

-- literal expression type-sanity
saneLit :: TAExpr -> Bool -> StateT Sanef IO [(TAExpr, String)]
saneLit l output = case l of
  ALit a lit -> do
    let isCorrectLitType = case lit of
          Intc _   -> a == TCons ("Prelude", "Int") []
          Floatc _ -> a == TCons ("Prelude", "Float") []
          Charc _  -> a == TCons ("Prelude", "Char") []
    wrongLitType <- do
      if isCorrectLitType then return [] else do
        let outl = show l ++ " has wrong literal type"
        lift $ when output $ putStrLn outl
        return [(l, outl)]
    state <- get
    let ty = currentType state
        qn = fName state
    if a == ty then return $ wrongLitType ++ [] else do
      let out = show qn
            ++ " is not type-sane."
            ++ " Literal type "
            ++ show a
            ++ " does not mathch expected type "
            ++ show ty
            ++ "."
      lift $ when output $ putStrLn out
      return $ wrongLitType ++ [(l, out)]
  _          -> error "SanityCheck.saneLit: no ALit"

-- search for a variable index and return its type (or nothing)
findgVar :: [(VarIndex, TypeExpr)] -> VarIndex -> Maybe TypeExpr
findgVar [] _             = Nothing
findgVar ((n, d) : gvs) i = if i == n then Just d else findgVar gvs i

-- typed expression type-sanity
saneTyped :: TAExpr -> Bool -> StateT Sanef IO [(TAExpr, String)]
saneTyped t output = case t of
  ATyped a expr _ -> do
    state <- get
    let ty = currentType state
        qn = fName state
    res <- do
      if a == ty then return [] else do
        let out = show qn
              ++ " is not type-sane."
              ++ " Types Expression type "
              ++ show a
              ++ " does not match expected type "
              ++ show ty
              ++ "."
        lift $ when output $ putStrLn out
        return [(t, out)]
    res2 <- saneExpr expr output
    return (res ++ res2)
  _               -> error "SanityCheck.saneTyped: no ATyped"

-- data kept in sanity state
data Sanef = Sanef { stateExpr   :: TAExpr
                   , globalVars  :: [(VarIndex, TypeExpr)]
                   , currentType :: TypeExpr
                   , fName       :: QName
                   }
