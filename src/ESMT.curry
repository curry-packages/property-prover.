------------------------------------------------------------------------------
--- This module provides some utility functions for the SMT-LIB language defined
--- in the package `smtlib` that are needed for checking Curry programs.
--- For example, functions for substituting sorts in terms, simplifying terms
--- and removing polymorphism in SMT-LIB scripts are provided.
---
--- @author  Michael Hanus
--- @version Juli 2021
------------------------------------------------------------------------------

module ESMT where

import Data.Either ( lefts )
import Data.List   ( (\\), intercalate, isPrefixOf, union )

import qualified Data.Map as FM
import Text.Pretty

import Language.SMTLIB.Goodies
import qualified Language.SMTLIB.Types as SMT

------------------------------------------------------------------------------
--- Sorts

-- Shows a sort as a string.
showSort :: SMT.Sort -> String
showSort (SMT.SComb s ss) = s ++ intercalate "_" (map showSort ss)

--- Does the sort represent a type parameter (`TVar i`)?
isTypeParameter :: SMT.Sort -> Bool
isTypeParameter (SMT.SComb s ss) =
  null ss && "TVar" `isPrefixOf` s && length s > 4

----------------------------------------------------------------------------
--- Terms

--- A constant with a sort declaration.
sortedConst :: SMT.Ident -> SMT.Sort -> SMT.Term
sortedConst c s = SMT.TComb (SMT.As c s) []

----------------------------------------------------------------------------
--- Function signatures

--- The signature of a function declaration.
data FunSig = FunSig SMT.Ident [SMT.Sort] SMT.Sort
  deriving (Eq, Show)

--- A definition of a polymorphic, possibly non-deterministic, operation.
--- The first component is a list of type paramters
--- which can be used in the type signature and the term.
--- The term in the third argument is the axiomatization of the function
--- definition. Thus, it contains all quantifiers and the equation
--- `(= (f x1...xn) rhs-term)` so that it can also be used to specify,
--- by exploiting disjunctions, the meaning of non-deterministic operations.
type FunSigTerm = ([SMT.Ident], FunSig, SMT.Term)

----------------------------------------------------------------------------
-- Smart constructors

--- Assert a simplified formula.
sAssert :: SMT.Term -> SMT.Command
sAssert = SMT.Assert . simpTerm

----------------------------------------------------------------------------
--- Examples:
{-
listType =
  DeclareDatatypes
    [("List",1,
      DT ["T"]
         [ DCons "nil" [],
           DCons "cons" [("car", SComb "T" []),
                         ("cdr", SComb "List" [SComb "T" []])]])]

maybeType =
  DeclareDatatypes
    [("Maybe",1,
      DT ["T"]
         [ DCons "Nothing" [],
           DCons "Just" [("just", SComb "T" [])]])]

pairType =
  DeclareDatatypes
    [("Pair",2,
      DT ["X", "Y"]
         [ DCons "mk-pair" [("first",  SComb "X" []),
                            ("second", SComb "Y" [])]])]
-}

---------------------------------------------------------------------------
-- All possibly sorted identifiers occurring in a SMT term.
allQIdsOfTerm :: SMT.Term -> [SMT.QIdent]
allQIdsOfTerm (SMT.TConst _)     = []
allQIdsOfTerm (SMT.TComb f args) = foldr union [f] (map allQIdsOfTerm args)
allQIdsOfTerm (SMT.Forall _ arg) = allQIdsOfTerm arg
allQIdsOfTerm (SMT.Exists _ arg) = allQIdsOfTerm arg
allQIdsOfTerm (SMT.Let bs e)     =
  foldr union [] $ map allQIdsOfTerm $ e : map snd bs
allQIdsOfTerm (SMT.Match e ps)   =
  foldr union [] $ map allQIdsOfTerm $ e : map snd ps
allQIdsOfTerm (SMT.Annot e _)    = allQIdsOfTerm e

-- All possibly sorted identifiers occurring in a define-sig element.
allQIdsOfSigs :: [FunSigTerm] -> [SMT.QIdent]
allQIdsOfSigs = foldr union [] . map allQIdsOfSig
 where allQIdsOfSig (_,_,t) = allQIdsOfTerm t

-- TODO: should be extended to all commands but currently sufficient
allQIdsOfAsserts :: [SMT.Command] -> [SMT.QIdent]
allQIdsOfAsserts = foldr union [] . map allQIdsOfAssert

allQIdsOfAssert :: SMT.Command -> [SMT.QIdent]
allQIdsOfAssert cmd = case cmd of SMT.Assert t -> allQIdsOfTerm t
                                  _            -> []

---------------------------------------------------------------------------
--- All type parameters occurring in a sort.
typeParamsOfSort :: SMT.Sort -> [SMT.Ident]
typeParamsOfSort s@(SMT.SComb sn ss) =
  if isTypeParameter s then [sn]
                       else foldr union [] (map typeParamsOfSort ss)

--- All type parameters contained in a term.
typeParamsOfTerm :: SMT.Term -> [SMT.Ident]
typeParamsOfTerm (SMT.TConst _)       = []
typeParamsOfTerm (SMT.TComb f args)   = foldr union (typeParamsOfQId f)
                                          (map typeParamsOfTerm args)
typeParamsOfTerm (SMT.Forall svs arg) =
  foldr union (typeParamsOfTerm arg) (map typeParamsOfSV svs)
typeParamsOfTerm (SMT.Exists svs arg) =
  foldr union (typeParamsOfTerm arg) (map typeParamsOfSV svs)
typeParamsOfTerm (SMT.Let bs e)       =
  foldr union [] $ map typeParamsOfTerm $ e : map snd bs
typeParamsOfTerm (SMT.Match e ps)     =
  foldr union [] $ map typeParamsOfTerm $ e : map snd ps
typeParamsOfTerm (SMT.Annot e _)      = typeParamsOfTerm e

typeParamsOfQId :: SMT.QIdent -> [SMT.Ident]
typeParamsOfQId (SMT.Id _  ) = []
typeParamsOfQId (SMT.As _ s) = typeParamsOfSort s

typeParamsOfSV :: SMT.SortedVar -> [SMT.Ident]
typeParamsOfSV (SMT.SV _ s) = typeParamsOfSort s

typeParamsOfFunSig :: FunSig -> [SMT.Ident]
typeParamsOfFunSig (FunSig _ ss s) =
  foldr union [] (map typeParamsOfSort (ss++[s]))

--- A type parameter substitution.
type TPSubst = FM.Map SMT.Ident SMT.Sort

--- The empty substitution
emptyTPSubst :: TPSubst
emptyTPSubst = FM.empty

----------------------------------------------------------------------------
--- Compute sort matching, i.e., if `matchSort t1 t2 = s`, then `t2 = s(t1)`.
matchSort :: SMT.Sort -> SMT.Sort -> Maybe TPSubst
matchSort s1@(SMT.SComb sn1 ss1) s2@(SMT.SComb sn2 ss2)
 | isTypeParameter s1
 = Just $ if s1 == s2
            then emptyTPSubst
            else FM.insert (head (typeParamsOfSort s1)) s2 emptyTPSubst
 | otherwise
 = if sn1 == sn2 then matchSorts ss1 ss2 else Nothing

matchSorts :: [SMT.Sort] -> [SMT.Sort] -> Maybe TPSubst
matchSorts []       []       = Just emptyTPSubst
matchSorts []       (_:_)    = Nothing
matchSorts (_:_)    []       = Nothing
matchSorts (t1:ts1) (t2:ts2) = do
  s <- matchSort t1 t2
  t <- matchSorts (map (substSort s) ts1)(map (substSort s) ts2)
  return (FM.union s t)

--- Applies a sort substitution to a sort.
substSort :: TPSubst -> SMT.Sort -> SMT.Sort
substSort sub (SMT.SComb sn ss) =
  maybe (SMT.SComb sn (map (substSort sub) ss)) id (FM.lookup sn sub)

--- Applies a sort substitution to a term.
substTerm :: TPSubst -> SMT.Term -> SMT.Term
substTerm sub term = case term of
  SMT.TConst _       -> term
  SMT.TComb f args   -> SMT.TComb (substQId sub f) (map (substTerm sub) args)
  SMT.Forall svs arg -> SMT.Forall (map (substSV sub) svs) (substTerm sub arg)
  SMT.Exists svs arg -> SMT.Forall (map (substSV sub) svs) (substTerm sub arg)
  SMT.Let bs e       -> SMT.Let (map (\ (v,s) -> (v, substTerm sub s)) bs)
                                (substTerm sub e)
  SMT.Match e ps     -> SMT.Match (substTerm sub e)
                                  (map (\(p,t) -> (p, substTerm sub t)) ps)
  SMT.Annot e as     -> SMT.Annot (substTerm sub e) as

substQId :: TPSubst -> SMT.QIdent -> SMT.QIdent
substQId _ qid@(SMT.Id _) = qid
substQId sub (SMT.As n s) = SMT.As n (substSort sub s)

substSV :: TPSubst -> SMT.SortedVar -> SMT.SortedVar
substSV sub (SMT.SV v s) = SMT.SV v (substSort sub s)

substFunSig :: TPSubst -> FunSig -> FunSig
substFunSig sub (FunSig fn ss s) =
  FunSig fn (map (substSort sub) ss) (substSort sub s)

substDefSig :: TPSubst -> FunSigTerm -> FunSigTerm
substDefSig tsub (ps, fsig, term) =
  (ps \\ FM.keys tsub, substFunSig tsub fsig, substTerm tsub term)

--------------------------------------------------------------------------
-- Rename identifiers.

rnmTerm :: (SMT.Ident -> SMT.Ident) -> SMT.Term -> SMT.Term
rnmTerm rnm term = case term of
  SMT.TConst _       -> term
  SMT.TComb f args   -> SMT.TComb (rnmQId rnm f) (map (rnmTerm rnm) args)
  SMT.Forall svs arg -> SMT.Forall svs (rnmTerm rnm arg)
  SMT.Exists svs arg -> SMT.Forall svs (rnmTerm rnm arg)
  SMT.Let bs e       -> SMT.Let (map (\ (v,s) -> (v, rnmTerm rnm s)) bs)
                                (rnmTerm rnm e)
  SMT.Match e ps     -> SMT.Match (rnmTerm rnm e)
                                  (map (\(p,t) -> (p, rnmTerm rnm t)) ps)
  SMT.Annot e as     -> SMT.Annot (rnmTerm rnm e) as

rnmQId :: (SMT.Ident -> SMT.Ident) -> SMT.QIdent -> SMT.QIdent
rnmQId rnm (SMT.Id n)   = SMT.Id (rnm n)
rnmQId rnm (SMT.As n s) = SMT.As (rnm n) s

rnmFunSig :: (SMT.Ident -> SMT.Ident) -> FunSig -> FunSig
rnmFunSig rnm (FunSig fn ss s) = FunSig (rnm fn) ss s

rnmDefSig :: (SMT.Ident -> SMT.Ident) -> ([SMT.Ident],FunSig,SMT.Term)
          -> ([SMT.Ident],FunSig,SMT.Term)
rnmDefSig rnm (ps, fsig, term) =
  (ps, rnmFunSig rnm fsig, rnmTerm rnm term)

--------------------------------------------------------------------------
-- A simplifier for terms:
simpTerm :: SMT.Term -> SMT.Term
simpTerm (SMT.TConst l) = SMT.TConst l
simpTerm (SMT.Let bs t) = if null bs then t'
                                 else SMT.Let bs' t'
 where bs' = map (\ (v,tm) -> (v, simpTerm tm)) bs
       t'  = simpTerm t
simpTerm (SMT.Forall vs t) = if null vs then t' else SMT.Forall vs t'
 where t' = simpTerm t
simpTerm (SMT.Exists vs t) = if null vs then t' else SMT.Exists vs t'
 where t' = simpTerm t
simpTerm (SMT.Match e ps)  = SMT.Match (simpTerm e)
                                       (map (\(p,t) -> (p, simpTerm t)) ps)
simpTerm (SMT.Annot t as)  = SMT.Annot (simpTerm t) as
simpTerm (SMT.TComb f ts)
 | unqual f == "/=" && length ts == 2
 = simpTerm (SMT.TComb (SMT.Id "not") [SMT.TComb (SMT.Id "=") ts])
 | f == SMT.Id "apply" && not (null ts')
 = case head ts' of SMT.TComb s' ts0 -> SMT.TComb s' (ts0 ++ tail ts')
                    _            -> fts
 | f == SMT.Id "not"
 = case ts' of [SMT.TComb s' [ts0]] -> if s' == f then ts0 else fts
               _                -> fts
 | f == SMT.Id "and"
 = case filter (/= true) ts' of
          []  -> true
          cjs -> if false `elem` cjs
                   then false
                   else SMT.TComb f (concatMap joinSame cjs)
 | f == SMT.Id "or"
 = case filter (/= false) ts' of
          []  -> false
          djs -> if true `elem` djs
                   then true
                   else SMT.TComb f (concatMap joinSame djs)
 | otherwise = fts
 where
  ts' = map simpTerm ts
  fts = SMT.TComb f ts'

  joinSame arg = case arg of SMT.TComb f' args | f==f' -> args
                             _                         -> [arg]

--------------------------------------------------------------------------
-- Remove As-identifiers if they are functions (for better readability):
reduceAsInTerm :: SMT.Term -> SMT.Term
reduceAsInTerm (SMT.TConst l)    = SMT.TConst l
reduceAsInTerm (SMT.Let bs t)    = SMT.Let
                                     (map (\ (v,tm) ->
                                             (v, reduceAsInTerm tm)) bs)
                                     (reduceAsInTerm t)
reduceAsInTerm (SMT.Forall vs t) = SMT.Forall vs (reduceAsInTerm t)
reduceAsInTerm (SMT.Exists vs t) = SMT.Exists vs (reduceAsInTerm t)
reduceAsInTerm (SMT.Match e ps)  = SMT.Match (reduceAsInTerm e)
                                             (map (\(p,t) ->
                                                    (p, reduceAsInTerm t)) ps)
reduceAsInTerm (SMT.Annot t as)  = SMT.Annot (reduceAsInTerm t) as
reduceAsInTerm (SMT.TComb f ts)  = SMT.TComb (simpAs f) (map reduceAsInTerm ts)
 where
  simpAs qid = case qid of SMT.As n (SMT.SComb s _) | s == "Func" -> SMT.Id n
                           _                                      -> qid

--------------------------------------------------------------------------
-- Get all sort identifiers occurring in a sort.
sortIdsOfSort :: SMT.Sort -> [SMT.Ident]
sortIdsOfSort (SMT.SComb s ss) = s : concatMap sortIdsOfSort ss

-- Get all sorts occurring in a term.
sortsOfTerm :: SMT.Term -> [SMT.Sort]
sortsOfTerm (SMT.TConst _)    = []
sortsOfTerm (SMT.Let bs t)    = concatMap (sortsOfTerm . snd) bs
                                ++ sortsOfTerm t
sortsOfTerm (SMT.Forall vs t) = map sortOfSortedVar vs ++ sortsOfTerm t
sortsOfTerm (SMT.Exists vs t) = map sortOfSortedVar vs ++ sortsOfTerm t
sortsOfTerm (SMT.Match e ps)  = concatMap (sortsOfTerm . snd) ps
                                ++  sortsOfTerm e
sortsOfTerm (SMT.Annot t _)   = sortsOfTerm t
sortsOfTerm (SMT.TComb f ts)  = sortsOfQIdent f ++ concatMap sortsOfTerm ts
 where
  sortsOfQIdent (SMT.Id _)   = []
  sortsOfQIdent (SMT.As _ s) = [s]

sortOfSortedVar :: SMT.SortedVar -> SMT.Sort
sortOfSortedVar (SMT.SV _ s) = s

--------------------------------------------------------------------------
-- Remove parametric polymorphism in an SMT script.
-- First, for all QIdents occurring in assertions, their type-instantiated
-- signatures are added. Then, for all QIdents occurring in these added
-- operations, their type-instantiated signatures are added and so forth,
-- until nothing needs to be added. Finally, the type-instantiated signatures
-- are renamed.
unpoly :: [Either [FunSigTerm] SMT.Command] -> [SMT.Command]
unpoly commands =
   let allsigs = map sigNameSort . concat . lefts $ commands
   in concatMap (unpolyCmd allsigs) . reverse . addSigs [] . reverse $ commands
 where
  addSigs :: [SMT.QIdent] -> [Either [FunSigTerm] SMT.Command]
          -> [Either [FunSigTerm] SMT.Command]
  addSigs _    []         = []
  addSigs qids (cmd:cmds) = case cmd of
    Left fts ->
      let (qids1,ftss) = addAllInstancesOfSigs (union (allQIdsOfSigs fts) qids)
                                               fts
      in Left ftss : addSigs qids1 cmds
    Right cmd' -> cmd : addSigs (union (allQIdsOfAssert cmd') qids) cmds

  -- remove remaining polymorphic signatures and rename qualified names
  -- according to their sorts
  unpolyCmd :: [(SMT.Ident, ([SMT.Ident],SMT.Sort))]
            -> Either [FunSigTerm] SMT.Command -> [SMT.Command]
  unpolyCmd sigs cmd = case cmd of
    Left fts -> funSigTermsToCommands $
                           map rnmTermInSig (filter (\ (ps,_,_) -> null ps) fts)
    Right (SMT.Assert term) -> [SMT.Assert (rnmQIdWithTInstTerm sigs term)]
    Right cmd' -> [cmd']
   where
    rnmTermInSig (ps,sig,term) = (ps, sig, rnmQIdWithTInstTerm sigs term)

-- Converts a list of function signatures into a list of commands that
-- axiomatize those functions.
funSigTermsToCommands :: [FunSigTerm] -> [SMT.Command]
funSigTermsToCommands fts = map
                              (\(_, (FunSig fn ss s), _) -> SMT.DeclareFun fn ss s)
                              fts
                            ++ concatMap (\(_, (FunSig fn _ _), term) ->
                                 [ SMT.Comment ""
                                 , SMT.Comment $ "Axiomatization of function '"
                                     ++ fn ++ "'"
                                 , sAssert term])
                               fts

-- Transforms a list of signatures into all its instances required by
-- sorted identifiers (second argument) and also required by sorted
-- identifiers in the added instances. Returns also the list of
-- remaining identifiers.
addAllInstancesOfSigs :: [SMT.QIdent] -> [FunSigTerm]
                      -> ([SMT.QIdent], [FunSigTerm])
addAllInstancesOfSigs allqids = addAllInsts allqids
 where
  addAllInsts qids fts =
    let (qids1,fts1) = addInstancesOfSigs qids fts
    in if null fts1
         then (qids1,fts)
         else let (qids2,fts2) = addAllInsts
                                   (union qids1 (allQIdsOfSigs fts1 \\ allqids))
                                   (fts ++ fts1)
              in (qids2, fts2)

-- Adds to given (polymorphic) define-sig elements all its type instances
-- required by qualified identifiers occurring in the first argument
-- provided that it does not already occur in the sig elements.
-- The list of unused qualified identifiers is also returned.
addInstancesOfSigs :: [SMT.QIdent] -> [FunSigTerm]
                   -> ([SMT.QIdent], [FunSigTerm])
addInstancesOfSigs qids allsigs = addInstsOfSigs qids allsigs
 where
  addInstsOfSigs qids0 []         = (qids0,[])
  addInstsOfSigs qids0 (fts:ftss) =
    let (qids1,fts1) = addInstancesOfSig qids0 allsigs fts
        (qids2,fts2) = addInstsOfSigs qids1 ftss
    in (qids2, fts1 ++ fts2)

-- Adds to a given (polymorphic) define-sig element all its type instances
-- required by qualified identifiers occurring in the first argument
-- provided that it does not already occur in the sig elements
-- contained in the second argument.
-- The list of unused qualified identifiers is also returned.
addInstancesOfSig :: [SMT.QIdent] -> [FunSigTerm] -> FunSigTerm
                  -> ([SMT.QIdent], [FunSigTerm])
addInstancesOfSig allqids allsigs fts@(ps, (FunSig fn ss rs), _) =
  addSigInsts allqids
 where
  addSigInsts :: [SMT.QIdent] -> ([SMT.QIdent], [FunSigTerm])
  addSigInsts []         = ([],[])
  addSigInsts (qid:qids) =
    let (qids1,sigs1) = addSigInsts qids
    in case qid of
         SMT.As n s | n==fn -> (qids1, sigInstForType s ++ sigs1)
         _              -> (qid : qids1, sigs1)

  sigInstForType s =
    maybe []
          (\tsub -> let rnm = toTInstName fn ps tsub
                    in if rnm fn `elem` map nameOfSig allsigs
                         then []
                         else [(rnmDefSig rnm (substDefSig tsub fts))])
          (matchSort (sigTypeAsSort ss rs) s)

--------------------------------------------------------------------------
-- Rename a sorted name w.r.t. its type instance of the polymorphic function.
-- For instance,
--     (As "id" (SComb "Func" [SComb "Int" [], SComb "Int" []]))
-- will be renamed to
--     (As "id_Int" (SComb "Func" [SComb "Int" [], SComb "Int" []]))
rnmQIdWithTInst :: [(SMT.Ident, ([SMT.Ident],SMT.Sort))] -> SMT.QIdent
                -> SMT.QIdent
rnmQIdWithTInst _ (SMT.Id n) = SMT.Id n
rnmQIdWithTInst sigs qid@(SMT.As n s) =
  maybe qid
        (\ (ps,psort) -> maybe qid
                               (\tsub -> SMT.As (addTInstName ps tsub n) s)
                               (matchSort psort s))
        (lookup n sigs)

-- Rename all sorted names occurring in a term w.r.t. its type instance
-- of the polymorphic function.
rnmQIdWithTInstTerm :: [(SMT.Ident, ([SMT.Ident],SMT.Sort))] -> SMT.Term
                    -> SMT.Term
rnmQIdWithTInstTerm sigs term = case term of
  SMT.TConst _ -> term
  SMT.TComb f args -> SMT.TComb (rnmQIdWithTInst sigs f)
                        (map (rnmQIdWithTInstTerm sigs) args)
  SMT.Forall svs arg -> SMT.Forall svs (rnmQIdWithTInstTerm sigs arg)
  SMT.Exists svs arg -> SMT.Forall svs (rnmQIdWithTInstTerm sigs arg)
  SMT.Let bs e -> SMT.Let (map (\ (v,s) -> (v, rnmQIdWithTInstTerm sigs s)) bs)
                  (rnmQIdWithTInstTerm sigs e)
  SMT.Match e ps -> SMT.Match (rnmQIdWithTInstTerm sigs e)
                              (map
                                (\(p,t) -> (p, rnmQIdWithTInstTerm sigs t)) ps)
  SMT.Annot e as -> SMT.Annot (rnmQIdWithTInstTerm sigs e) as

-- Renaming operation which changes the name of a given (polymorphic)
-- function w.r.t. a list of type parameters and a substitution.
toTInstName :: SMT.Ident -> [SMT.Ident] -> TPSubst -> SMT.Ident -> SMT.Ident
toTInstName fn ps tsub n | fn == n   = addTInstName ps tsub n
                         | otherwise = n

-- Add a sort index to a name of a (polymorphic) function w.r.t.
-- a list of type parameters and a type substitution.
addTInstName :: [SMT.Ident] -> TPSubst -> SMT.Ident -> SMT.Ident
addTInstName tps tsub n =
  n ++ concatMap (\p -> maybe "" (('_':) . showSort) (FM.lookup p tsub)) tps

-- The name of a signature.
nameOfSig :: FunSigTerm -> SMT.Ident
nameOfSig (_, FunSig n _ _, _) = n

-- The name and sort of a signature.
sigNameSort :: FunSigTerm -> (SMT.Ident, ([SMT.Ident],SMT.Sort))
sigNameSort (ps, FunSig n ss s, _) = (n, (ps, sigTypeAsSort ss s))

sigTypeAsSort :: [SMT.Sort] -> SMT.Sort -> SMT.Sort
sigTypeAsSort [] s = s
sigTypeAsSort (t:ts) s = SMT.SComb "Func" [t, sigTypeAsSort ts s]
