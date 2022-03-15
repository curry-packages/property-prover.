--- -----------------------------------------------------------------------------
--- Flattening
--- @author  Björn Peemöller
--- @version April 2015
--- -----------------------------------------------------------------------------
module Inference.Flattening where

import           Data.List                   ( intersect, mapAccumL, partition )
import           Data.Tuple.Extra            ( second )
import           FlatCurry.Annotated.Goodies
import           FlatCurry.Annotated.Types

--- A flattening takes an additional list of fresh variables
type Flattening a = [VarIndex] -> a -> ([VarIndex], a)

--- Flatten a program
flattenProg :: Flattening (AProg a)
flattenProg xs (AProg m is ty fs os) = (xs1, AProg m is ty fs' os)
 where
  (xs1, fs') = flattenFuncs xs fs

flattenFuncs :: Flattening [AFuncDecl a]
flattenFuncs = mapAccumL flattenFunc

--- Flatten a function
flattenFunc :: Flattening (AFuncDecl a)
flattenFunc xs (AFunc f a v ty r) = second (AFunc f a v ty) (flattenRule xs r)

--- Flatten a rule
flattenRule :: Flattening (ARule a)
flattenRule xs (ARule a vs e)  = second (ARule a vs) (flattenExpr xs e)
flattenRule xs (AExternal a s) = (xs, AExternal a s)

--- Flatten an expression
flattenExpr :: Flattening (AExpr a)
flattenExpr xs v@(AVar _ _) = (xs, v)
flattenExpr xs l@(ALit _ _) = (xs, l)
flattenExpr xs (AComb a ct qn es) = let (xs1, ds, es') = splitArgs xs es
                                    in (xs1, flatLet ds (AComb a ct qn es'))
flattenExpr xs (AFree a vs e) = let (xs1, e') = flattenExpr xs e
                                in (xs1, AFree a vs e')
flattenExpr xs (ALet _ ds e)
  = let (xs1, ds') = mapAccumL flatD xs ds -- type argument of ALet?
        (xs2, e')  = flattenExpr xs1 e
    in (xs2, flatLet ds' e')
 where
  flatD ys (v, ve) = let (ys1, ve') = flattenExpr ys ve
                     in (ys1, (v, ve'))
flattenExpr xs (AOr a e1 e2) = let (xs1, e1') = flattenExpr xs e1
                                   (xs2, e2') = flattenExpr xs1 e2
                               in (xs2, AOr a e1' e2')
flattenExpr xs (ACase a ct e bs)
  = let (xs1, e')  = flattenExpr xs e
        (xs2, bs') = mapAccumL flatB xs1 bs
        ea         = annExpr e
        (x : xs3)  = xs2
    in case e of
         AVar _ _ -> (xs2, ACase a ct e' bs')
         _        -> (xs3, flatLet [((x, ea), e)] (ACase a ct (AVar ea x) bs'))
 where
  flatB ys (ABranch p be) = let (ys1, be') = flattenExpr ys be
                            in (ys1, ABranch p be')
flattenExpr xs (ATyped a e ty) = let (xs1, e') = flattenExpr xs e
                                 in (xs1, ATyped a e' ty)

--- @splitArgs xs es = (xs', ds, es')@ replaces all non-variable
--- expressions in @es@ by new variables subsequently taken from @xs@,
--- and generates the bindings @ds@ for those lifted expressions.
--- That is, @es'@ consists of variables only, originating either from @es@
--- or from @xs@, such that $es'[ds] = es$, i.e., replacing the extracted
--- bindings again should yield the original list.
--- @xs'@ is xs without the extracted variables.
splitArgs :: [VarIndex]
          -> [AExpr a]
          -> ([VarIndex], [((VarIndex, a), AExpr a)], [AExpr a])
splitArgs xs []       = (xs, [], [])
splitArgs xs (e : es) = case e of
  AVar _ _ -> let (xs', ds, es') = splitArgs xs es -- type argument of ALet?
              in (xs', ds, e : es')
  _        -> let (x' : xs', e') = flattenExpr xs e
                  (xs2, ds, es') = splitArgs xs' es
                  a'             = annExpr e'
              in (xs2, ((x', a'), e') : ds, AVar a' x' : es')

--- @flatLet ds e@ lifts nested let-declarations in ds to the top-level.
--- In addition, if `e` has the form `Let ds' e'`, the bindings `ds'` are
--- also lifted upwards.
flatLet :: [((VarIndex, a), AExpr a)] -> AExpr a -> AExpr a
flatLet decls ex = case liftDecls decls of
  []  -> ex
  ds' -> case ex of
    ALet a ds'' e' -> ALet a (ds' ++ ds'') e'
    _              -> ALet (annExpr ex) ds' ex
 where
  liftDecls :: [((VarIndex, a), AExpr a)] -> [((VarIndex, a), AExpr a)]
  liftDecls []            = []
  liftDecls ((x, d) : ds) = case d of
    ALet _ ds1 e -> ds1 ++ (x, e) : liftDecls ds -- type argument of ALet?
    _            -> (x, d) : liftDecls ds