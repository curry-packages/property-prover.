--- -----------------------------------------------------------------------------
--- Simplification
--- @author  Björn Peemöller
--- @version April 2015
--- -----------------------------------------------------------------------------

module Inference.Simplification where

import           Data.List                   ( mapAccumL, maximum, nub )
import           Data.Tuple.Extra            ( second )
import           FlatCurry.Annotated.Goodies
import           FlatCurry.Annotated.Types

--- Simplify an annotated expression
simplifyExpr :: Eq a => AExpr a -> AExpr a
simplifyExpr = trExpr AVar ALit AComb cLet AFree AOr cCase ABranch ATyped
 where
  -- compression of let-declarations
  cLet a ds e | ds == ds' && e == e' = if null ds' then e' else ALet a ds' e'
              | otherwise = cLet a ds' e'
   where
    (ds', e') = cLet' [] ds

    cLet' bs0 [] = (bs0, e)
    cLet' bs1 (b : bs2)
      | isInlineable b = (map (second replace) (bs1 ++ bs2), replace e)
      | otherwise = cLet' (bs1 ++ [b]) bs2
     where
      isInlineable bd = isSimple bd || not (isShared bd)

      isShared ((v, _), _) = count v (concatMap freeVarsDup (e : map snd ds)) > 1

      replace         = simplifyExpr
        . updVars (\a v -> if v == fst (fst b) then snd b else AVar a v)

      count x xs = length $ filter (== x) xs

    isSimple ((v, a), ve) = case ve of
      AVar _ x        -> x /= v -- do not replace recursive bindings
                             -- such as let ones = 1 : ones in ones
      ALit _ _        -> True
      AComb _ ct _ es -> (ct == ConsCall || isPartCall ct)
        && all (curry isSimple (v, a)) es
      _               -> isFailed ve

  -- Compression of case expressions: When the scrutinized expression is either
  -- a literal or a constructor call, the respective branch is searched for.
  -- If such a branch exists, the expressions reduces to the branch's
  -- right-hand-side, otherwise the expression reduces to `failed`.
  -- Also removes case expressions where all branches are the same.
  cCase a ct e bs | allEqual (map branchExpr bs) = branchExpr (head bs)
                  | otherwise = case e of
    ALit a' l -> case findBranch (ALPattern a' l) bs of
      Nothing      -> failedExpr a
      Just (_, be) -> be
    AComb a' ConsCall c es -> case findBranch (APattern a' c []) bs of
      Nothing       -> failedExpr a
      Just (xs, be) -> simplifyExpr (unfold xs es be)
    _ -> if null bs then failedExpr a else ACase a ct e bs

allEqual :: Eq a => [a] -> Bool
allEqual [] = False
allEqual (x:xs) = all (==x) xs

--- Simple unfolding
unfold :: [(VarIndex, a)] -> [AExpr a] -> AExpr a -> AExpr a
unfold vs es e = if null binds then e' else ALet (annExpr e') binds e'
 where
  binds              = zip vs' es

  (ARule a vs' e')   = freshRule (maximumVarIndex es + 1) (ARule a vs e)

  maximumVarIndex es = maximum (0 : concatMap allVars es)

--- Get all free variables of an expression, with duplicates.
freeVarsDup :: AExpr a -> [VarIndex]
freeVarsDup (AVar _ v) = [v]
freeVarsDup (ALit _ _) = []
freeVarsDup (AComb _ _ _ es) = concatMap freeVarsDup es
freeVarsDup (AFree _ vs e) = freeVarsDup e \\\ map fst vs
freeVarsDup (AOr _ e1 e2) = freeVarsDup e1 ++ freeVarsDup e2
freeVarsDup (ACase _ _ e bs) = concat (freeVarsDup e : map inBranch bs)
 where
  inBranch (ABranch p be) = freeVarsDup be \\\ map fst (patVars p)
freeVarsDup (ALet _ bs e) = concatMap freeVarsDup (e : es) \\\ map fst vs
 where
  (vs, es) = unzip bs
freeVarsDup (ATyped _ e _) = freeVarsDup e

--- List difference with duplicates.
(\\\) :: Eq a => [a] -> [a] -> [a]
xs \\\ ys = filter (`notElem` nub ys) xs

--- Select the pattern variables of a given pattern
patVars :: APattern a -> [(VarIndex, a)]
patVars (APattern _ _ vs) = vs
patVars (ALPattern _ _)   = []

--- Create a fresh variant of a rule by numbering all variables
--- from `i` onwards.
freshRule :: VarIndex -> ARule a -> ARule a
freshRule i = snd . rnRule [i ..]

takeVars :: [VarIndex] -> [a] -> ([VarIndex], [VarIndex])
takeVars fresh []          = (fresh, [])
takeVars (f : fs) (_ : os) = let (fs', os') = takeVars fs os
                             in (fs', f : os')
takeVars [] (_ : _)        = error "Renaming.takeVars: no more fresh variables"

--- Find the matching branch for a given pattern.
findBranch :: APattern a -> [ABranchExpr a] -> Maybe ([(VarIndex, a)], AExpr a)
findBranch _ []                 = Nothing
findBranch p (ABranch q e : bs) | eqPattern p q = Just (patVars q, e)
                                | otherwise = findBranch p bs

--- Check if two pattern are equal.
eqPattern :: APattern a -> APattern a -> Bool
eqPattern p1 p2 = case (p1, p2) of
  (APattern _ (f, _) _, APattern _ (g, _) _) -> f == g
  (ALPattern _ l, ALPattern _ m) -> l == m
  _ -> False

-- -----------------------------------------------------------------------------
-- Implementation of renaming
-- -----------------------------------------------------------------------------
type Renaming a = [VarIndex] -> a -> ([VarIndex], a)

--- Renaming of a 'Prog', i.e., all variables occurring in the 'Prog'
--- get renamed to @v1@, @v2@, ... consistently ($\alpha$-conversion).
rnProg :: Renaming (AProg a)
rnProg xs (AProg m is ty fs os) = (xs1, AProg m is ty fs' os)
 where
  (xs1, fs') = mapAccumL rnFunc xs fs

--- Renaming of a function declaration.
rnFunc :: Renaming (AFuncDecl a)
rnFunc xs (AFunc f a v ty r) = second (AFunc f a v ty) (rnRule xs r)

--- Renaming of a function rule.
rnRule :: Renaming (ARule a)
rnRule xs (ARule a vs e)  = let (xs1, vs') = takeVars xs vs
                                (xs2, e')  = rnExpr (zip (map fst vs) vs') xs1 e
                            in (xs2, ARule a (swapAnn vs' vs) e')
rnRule xs (AExternal a s) = (xs, AExternal a s)

--- Renaming of an expression.
rnExpr :: [(VarIndex, VarIndex)] -> Renaming (AExpr a)
rnExpr ren xs (AVar a x)         = case lookup x ren of
  Nothing -> (xs, AVar a x)
  Just w  -> (xs, AVar a w)
rnExpr _ xs l@(ALit _ _)         = (xs, l)
rnExpr ren xs (AComb a ct qn es) = let (xs1, es') = mapAccumL (rnExpr ren) xs es
                                   in (xs1, AComb a ct qn es')
rnExpr ren xs (AFree a vs e)
  = let (xs1, vs') = takeVars xs vs
        vsNoAnn    = map fst vs
        ren1       = zip vsNoAnn vs' ++ filter ((`notElem` vsNoAnn) . fst) ren
        (xs2, e')  = rnExpr ren1 xs1 e
    in (xs2, AFree a (swapAnn vs' vs) e')
rnExpr ren xs (ALet a ds e)
  = let (vs, es)   = unzip ds
        (xs1, vs') = takeVars xs ds
        vsNoAnn    = map fst vs
        ren1       = zip vsNoAnn vs' ++ filter ((`notElem` vsNoAnn) . fst) ren
        (xs2, es') = mapAccumL (rnExpr ren1) xs1 es
        (xs3, e')  = rnExpr ren1 xs2 e
    in (xs3, ALet a (zip (swapAnn vs' vs) es') e')
rnExpr ren xs (AOr a e1 e2)      = let (xs1, e1') = rnExpr ren xs e1
                                       (xs2, e2') = rnExpr ren xs1 e2
                                   in (xs2, AOr a e1' e2')
rnExpr ren xs (ACase a ct e bs)
  = let (xs1, e')  = rnExpr ren xs e
        (xs2, bs') = mapAccumL (rnBranchExpr ren) xs1 bs
    in (xs2, ACase a ct e' bs')
rnExpr ren xs (ATyped a e ty)    = let (xs1, e') = rnExpr ren xs e
                                   in (xs1, ATyped a e' ty)

rnBranchExpr :: [(VarIndex, VarIndex)] -> Renaming (ABranchExpr a)
rnBranchExpr ren ys (ABranch (APattern a p zs) be)
  = let (ys1, zs') = takeVars ys zs
        zsNoAnn    = map fst zs
        ren1       = zip zsNoAnn zs' ++ filter ((`notElem` zsNoAnn) . fst) ren
        (ys2, be') = rnExpr ren1 ys1 be
    in (ys2, ABranch (APattern a p (swapAnn zs' zs)) be')
rnBranchExpr ren ys (ABranch l@(ALPattern _ _) be)
  = let (ys1, be') = rnExpr ren ys be
    in (ys1, ABranch l be')

rnPattern :: Renaming (APattern a)
rnPattern xs (APattern a p ys) = let (as, bs) = takeVars xs ys
                                 in (as, APattern a p (swapAnn bs ys))
rnPattern xs l@(ALPattern _ _) = (xs, l)

--- Annotated FlatCurry expression representing `failed`
failedExpr :: TypeAnn -> AExpr TypeAnn
failedExpr ann = AComb ann FuncCall (("Prelude", "failed"), ann) []

--- Is the given expression equal to `failed`?
isFailed :: AExpr a -> Bool
isFailed e = case e of
  AComb _ FuncCall (("Prelude", "failed"), _) [] -> True
  _ -> False

swapAnn :: [a] -> [(b, c)] -> [(a, c)]
swapAnn = zipWith (\x (_, a) -> (x, a))

--- Check if given combination type is a partial call
isPartCall :: CombType -> Bool
isPartCall ct = case ct of
  ConsPartCall _ -> True
  FuncPartCall _ -> True
  _              -> False