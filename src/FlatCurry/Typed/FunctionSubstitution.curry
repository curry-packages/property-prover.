module FlatCurry.Typed.FunctionSubstitution
  ( substf
  , substFuncCall
  , makeTE
  , substTypes
  , findSubsts
  ) where

import           Data.List                   ( find, maximum )
import           FlatCurry.Annotated.Goodies ( annExpr, funcArgs, funcBody )
import           FlatCurry.Annotated.Types
import           FlatCurry.Typed.Types

-----------------------SUBSTITUTION METHOD-----------------------
-- @param funcd: function declaration of the function that is being inlined
-- @param gexprs: arguments that have been applied to the function
-- @param n: maximum global variable in g
substFuncCall :: TAFuncDecl -> [TAExpr] -> VarIndex -> TAExpr
substFuncCall funcd gexprs n
  = let fargs        = funcArgs funcd
        rhs          = funcBody funcd
        (ns, ftypes) = unzip fargs
        m            = maximum (0 : ns)
        rhs'         = adaptLokalVars (max n m) m rhs
        gtypes       = map annExpr gexprs
        substs       = findSubsts ftypes gtypes
        rhs''        = substTypes substs rhs'
        ngexs        = zip ns gexprs
    in substf ngexs rhs''

-- substitute every variable by their corresponding expression 
-- @param gargs (i,e) : e will substitue every occurence of AVar _ i
-- @param expr : the expression wherein we seek to substitue the variables
substf :: [(VarIndex, TAExpr)] -> TAExpr -> TAExpr
substf gargs expr = case expr of
  AVar _ i           -> case find (\(x, _) -> x == i) gargs of
    Just (_, e) -> e
    Nothing     -> expr
  ALit _ _           -> expr
  AComb a ct q exprs -> AComb a ct q (map (substf gargs) exprs)
  ALet a lets ex     -> let (ia, exs) = unzip lets
                            lets'     = zip ia (map (substf gargs) exs)
                        in ALet a lets' (substf gargs ex)
  AFree a ia ex      -> AFree a ia (substf gargs ex)
  AOr a ex1 ex2      -> AOr a (substf gargs ex1) (substf gargs ex2)
  ACase a ct ex brs  ->
    let brs' = map (\(ABranch p e) -> ABranch p (substf gargs e)) brs
    in ACase a ct (substf gargs ex) brs'
  ATyped a ex ty     -> ATyped a (substf gargs ex) ty

-- @param ftypes: types of the arguments from the function to be inlined
-- @param gtypes: types of the arguments given to the funtioncall
findSubsts :: [TypeExpr] -> [TypeExpr] -> [(TypeExpr, TypeExpr)]
findSubsts [] [] = []
findSubsts (_ : _) [] = error
  $ "FuncSubstitution.findSubsts:"
  ++ "argument lists do not have the same length!"
findSubsts [] (_ : _) = error
  $ "FuncSubstitution.findSubsts:"
  ++ "argument lists do not have the same lentgh!"
findSubsts (f : ftypes) (g : gtypes) = case f of
  TVar _         -> (f, g) : findSubsts ftypes gtypes
  FuncType f1 f2 -> case g of
    FuncType g1 g2 ->
      findSubsts [f1] [g1] ++ findSubsts [f2] [g2] ++ findSubsts ftypes gtypes
    ForallType _ _ -> fat
    _              ->
      error $ "FuncStubstitution.findSubsts:" ++ " f is FuncType but g is not."
  TCons _ tf     -> case g of
    TCons _ tg     -> findSubsts tf tg ++ findSubsts ftypes gtypes
    ForallType _ _ -> fat
    _              ->
      error $ "FuncSubstitution.findSubsts:" ++ " f is TCons but g is not" --TODO: think, could this happen?
  ForallType _ _ -> fat
 where
  fat = error
    $ "Found FORALLTYPE. Simplification not possible. "
    ++ "See manual for more information."

-- substitute the type expressions in an expression
-- @param subs: list of substitutions 
-- @param expr: the expression wherein the types are possibly being substitued
substTypes :: [(TypeExpr, TypeExpr)] -> TAExpr -> TAExpr
substTypes subs expr = case expr of
  AVar a i                -> AVar (substTypesT subs a) i
  ALit _ _                -> expr
  AComb a ct (q, b) exprs -> AComb (substTypesT subs a) ct
    (q, substTypesT subs b) (map (substTypes subs) exprs)
  ALet a lets ex          ->
    let (ia, exs) = unzip lets
        ia'       = map (\(i, aa) -> (i, substTypesT subs aa)) ia
        exs'      = map (substTypes subs) exs
        lets'     = zip ia' exs'
    in ALet (substTypesT subs a) lets' (substTypes subs ex)
  AFree a va ex           -> AFree (substTypesT subs a)
    (map (\(i, b) -> (i, substTypesT subs b)) va) (substTypes subs ex)
  AOr a ex1 ex2           -> AOr (substTypesT subs a) (substTypes subs ex1)
    (substTypes subs ex2)
  ACase a ct ex brs       -> ACase (substTypesT subs a) ct (substTypes subs ex)
    (map (substTypesBr subs) brs)
  ATyped a ex ty          -> ATyped (substTypesT subs a) (substTypes subs ex)
    (substTypesT subs ty)

-- handle type substitution in branches
substTypesBr :: [(TypeExpr, TypeExpr)] -> TABranchExpr -> TABranchExpr
substTypesBr subs branch = case branch of
  ABranch (APattern a (q, b) va) ex -> ABranch
    (APattern (substTypesT subs a) (q, substTypesT subs b)
     (map (\(v, c) -> (v, substTypesT subs c)) va)) (substTypes subs ex)
  ABranch (ALPattern a l) ex        -> ABranch (ALPattern a l)
    (substTypes subs ex)

-- substitute a type variable by a given type
-- @param subs: list of substitutions 
-- @param ty: type expression wherein the type variables will be substituted
substTypesT :: [(TypeExpr, TypeExpr)] -> TypeExpr -> TypeExpr
substTypesT subs ty = case ty of
  TVar _         -> case find (\(tf, _) -> ty == tf) subs of
    Just (_, g) -> g
    Nothing     -> ty
  FuncType t1 t2 -> FuncType (substTypesT subs t1) (substTypesT subs t2)
  TCons q tys    -> TCons q (map (substTypesT subs) tys)
  ForallType i t -> ForallType i (substTypesT subs t)

-- make a TypeExpression by a given list of expressions and a result type
makeTE :: [TAExpr] -> TypeExpr -> TypeExpr
makeTE es a = foldr (FuncType . annExpr) a es

-- Adapt variable names of local variables. Local variables are those
-- that are defined in the rhs of a function 
-- (e.g. by let, free, or case expressions).
-- @param n: maximum global VarIndex of the current function 
-- @param m: maximum VarIndex of variables given to the expression 
--           (everything above is a lokal variable)
adaptLokalVars :: Int -> Int -> TAExpr -> TAExpr
adaptLokalVars n m expr = case expr of
  AVar a i           -> if i > m then AVar a (n + (i - m)) else expr
  ALit _ _           -> expr
  AComb a ty q exprs -> AComb a ty q (map (adaptLokalVars n m) exprs)
  ALet a lets exp    ->
    let (ias, exs) = unzip lets
        (is, as)   = unzip ias
        is'        = map (adaptLokalIs n m) is
        exs'       = map (adaptLokalVars n m) exs
    in ALet a (zip (zip is' as) exs') (adaptLokalVars n m exp)
  AFree a frees exp  -> let (is, as) = unzip frees
                            is'      = map (adaptLokalIs n m) is
                        in AFree a (zip is' as) (adaptLokalVars n m exp)
  AOr a ex1 ex2      -> AOr a (adaptLokalVars n m ex1) (adaptLokalVars n m ex2)
  ACase a ct exp brs -> ACase a ct (adaptLokalVars n m exp)
    (map (adaptLokalVarsBr n m) brs)
  ATyped a exp t     -> ATyped a (adaptLokalVars n m exp) t

adaptLokalIs :: Int -> Int -> VarIndex -> VarIndex
adaptLokalIs n m vi = if vi > m then n + (vi - m) else vi

adaptLokalVarsBr :: Int -> Int -> TABranchExpr -> TABranchExpr
adaptLokalVarsBr n m br = case br of
  ABranch (APattern a q pvs) exp ->
    let (is, as) = unzip pvs
        is'      = map (adaptLokalIs n m) is
    in ABranch (APattern a q (zip is' as)) (adaptLokalVars n m exp)
  ABranch (ALPattern a l) exp    -> ABranch (ALPattern a l)
    (adaptLokalVars n m exp)

