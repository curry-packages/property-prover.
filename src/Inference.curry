module Inference where

import           Analysis.ProgInfo
import           Analysis.TotallyDefined     ( siblingCons )
import           Data.Char                   ( toUpper )
import           Data.List
  ( (\\), maximum, nub, partition, union )
import qualified Data.Map                    as DM
import           Data.Maybe
  ( fromJust, fromMaybe, isNothing, mapMaybe )
import           Debug.Trace
import           FlatCurry.Annotated.Goodies
  ( allVars, allVarsInFunc, annExpr, branchPattern, patCons, unAnnExpr
  , unAnnFuncDecl )
import           FlatCurry.Annotated.Pretty  ( ppFuncDecl )
import qualified FlatCurry.Goodies           as FCG
import           FlatCurry.ShowIntMod        ( showFuncDeclAsFlatCurry )
import           FlatCurry.Typed.Goodies
import           FlatCurry.Typed.Types
import           FlatCurry.Types
import           Flattening
import           Simplification
import           Text.Pretty                 ( pPrint )
import           Utils                       ( encodeSpecialChars )

type InfInfo = (QName, Bool, [QName], [TAFuncDecl])

inferNFConds :: ModuleName
             -> ProgInfo (TypeDecl, [Constructor])
             -> [TAFuncDecl]
             -> [TAFuncDecl]
inferNFConds modname info fdecls
  = let freshVars      = [maximum (concatMap allVarsInFunc fdecls) + 1 ..]
        (_, flatDecls) = flattenFuncs freshVars fdecls
        res            = map (inferNF modname info) flatDecls
        decls          = filterRelevantNFCs modname res
    in map unrec decls

filterRelevantNFCs :: ModuleName -> [InfInfo] -> [TAFuncDecl]
filterRelevantNFCs modname res = fds
 where
  canFail
    = [r | r@((mname, _), canFail, _, _) <- res, mname == modname && canFail]

  calledQNs = nub [qn | (_, _, qns, _) <- canFail, qn <- qns]

  fds = [fd | (_, _, _, ds) <- canFail `union` called calledQNs [], fd <- ds]

  called :: [QName] -> [InfInfo] -> [InfInfo]
  called qns is
    = if qns == qns' then is `union` is' else called qns' (is `union` is')
   where
    is'  = nub [info | qn <- qns, info@(qn', _, _, _) <- res, qn == qn']

    qns' = nub (qns ++ concatMap (\(qn, _, cqns, _) -> qn : cqns) is')

inferNF
  :: ModuleName -> ProgInfo (TypeDecl, [Constructor]) -> TAFuncDecl -> InfInfo
inferNF modname info f@(AFunc qn@(mname, fname) arity vis ty rule) =
   --(if fname == "max" then trace (show f ++ show fdecls) else id)
  (qn, canFail, calls, fdecls)
 where
  argtys                  = FCG.argTypes ty

  nftype                  = foldr FuncType boolType argtys

  ty'                     = foldr FuncType boolType
    (replicate arity boolType ++ argtys)

  qn' s = (mname, fname ++ s)

  (canFail, calls, rule') = inferNFRule info arity ty' rule

  expr'                   = isTrivialRule rule'

  callRule                = inferNFCallRule arity nftype ty'
    (qn' "_nonfailspec") rule expr'

  fdecls
    = [ AFunc (qn' "'nonfail") arity vis nftype callRule
      , AFunc (qn' "_nonfailspec") (2 * arity) vis ty' rule'
      ]

isTrivialRule :: TARule -> Maybe TAExpr
isTrivialRule (AExternal _ _)  = Nothing
isTrivialRule (ARule _ _ expr) = case expr of
  AComb _ _ (qn, _) _ -> case qn of
    ("Prelude", "True")  -> Just expr
    ("Prelude", "False") -> Just expr
    _                    -> Nothing
  _                   -> Nothing

inferNFRule :: ProgInfo (TypeDecl, [Constructor])
            -> Int
            -> TypeExpr
            -> TARule
            -> (Bool, [QName], TARule)
inferNFRule _ _ _ r@(AExternal _ _) = (False, [], r)
inferNFRule info arity ty' (ARule _ argVars expr)
  | canFail = (canFail, calls, ARule ty' argVars' expr')
  | otherwise = (False, [], ARule ty' (argVars' ++ rhsVars) (boolExpr "True")) -- Calls of non-failing functions can be omitted
 where
  (canFail, calls, expr')   = inferNFExpr info expr

  argVars'                  = bArgs ++ argVars

  argIndxs                  = map fst argVars'

  freshVar                  = maximum (argIndxs ++ allVars expr') + 1

  rhsVars                   = drop (length argVars')
    (addTypes2Vars (argIndxs ++ [freshVar ..]) (stripForall ty'))

  addTypes2Vars (v : vs) ty = case ty of
    FuncType t1 t2 -> (v, t1) : addTypes2Vars vs t2
    _              -> []

  bArgs                     = map (\(v, _) -> (starVar v, boolType)) argVars

inferNFCallRule
  :: Int -> TypeExpr -> TypeExpr -> QName -> TARule -> Maybe TAExpr -> TARule
inferNFCallRule _ _ _ _ r@(AExternal _ _) _ = r
inferNFCallRule arity nftype ty' qn (ARule _ argVars _) texp = ARule nftype
  (argVars ++ rhsVars) expr
 where
  expr = case texp of
    Nothing -> AComb boolType FuncCall (qn, ty')
      (replicate (length argVars) (boolExpr "True")
       ++ map (\(i, t) -> AVar t i) argVars)
    Just e  -> e

  argIndxs = map fst argVars

  freshVar = maximum (argIndxs ++ allVars expr) + 1

  rhsVars = drop (length argVars)
    (addTypes2Vars (argIndxs ++ [freshVar ..]) (stripForall nftype))

  addTypes2Vars (v : vs) ty = case ty of
    FuncType t1 t2 -> (v, t1) : addTypes2Vars vs t2
    _              -> []

starVar :: Int -> Int
starVar = (+ 10000)

starVarExp :: TAExpr -> TAExpr
starVarExp e = case e of
  AVar _ i -> AVar boolType (starVar i)
  _        -> error $ "Function argument must be variable but found " ++ show e

-- TODO: type annotations => type as result?
inferNFExpr
  :: ProgInfo (TypeDecl, [Constructor]) -> TAExpr -> (Bool, [QName], TAExpr)
inferNFExpr info expr
  = let inf = inferNFExpr info
    in case expr of
         AVar ty i -> (False, [], AVar boolType (starVar i)) -- TODO: addConsts to more cases?
         ALit _ _ -> (False, [], boolExpr "True")
         AComb _ _ (("Prelude", "failed"), _) [] ->
           (True, [], boolExpr "False")
         AComb _ _ (("Prelude", "error"), _) _ -> (True, [], boolExpr "False")
         AComb _ ConsCall _ _ -> (False, [], boolExpr "True")
         AComb _ (ConsPartCall _) _ _ -> (False, [], boolExpr "True")
         AComb _ FuncCall ((_, '_' : 'i' : 'm' : 'p' : 'l' : _), _) _ ->
           (False, [], boolExpr "True") -- TODO: Implement whitelist?
         AComb ty FuncCall (("Prelude", "apply"), _) _ ->
           (False, [], boolExpr "True")
         AComb _ FuncCall (qn@(modname, fun), qnty) es
           | isHO qnty -> (False, [], boolExpr "True")
           | otherwise ->
             ( False
             , [qn]
             , AComb boolType FuncCall
               ((modname, fun ++ "_nonfailspec"), nonFailType qnty)
               (map starVarExp es ++ es)
             )
          where
           isHO :: TypeExpr -> Bool
           isHO t = case t of
             FuncType (FuncType _ _) _ -> True
             FuncType _ t -> isHO t
             _ -> False
         AComb _ (FuncPartCall n) (qn@(modname, fun), qnty) es ->
           (False, [], boolExpr "True")
          --  ( False
          --  , [qn]
          --  , AComb boolType (FuncPartCall n)
          --    ((modname, fun ++ "_nonfailspec"), nonFailType qnty) es -- Intertwine arguments with Boolean values?
          --  )
         ALet _ binds e ->
           let (b, qs, e')          = inf e
               (bs, qss, starBinds) = unzip3
                 (map (\((v, _), exp) ->
                       let (b2, qs2, exp') = inf exp
                       in (b2, qs2, ((starVar v, boolType), exp'))) binds)
           in ( b || or bs
              , qs ++ concat qss
              , ALet boolType (starBinds ++ binds) e'
              )
         AOr _ e1 e2 ->
           let (b1, qs1, e1') = inf e1
               (b2, qs2, e2') = inf e2
               canFail        = b1 || b2
           in if canFail
                then (True, [], boolExpr "False")
                else (b1 || b2, qs1 `union` qs2, AOr boolType e1' e2')
         ACase _ ct e brs ->
           let (mdecl, misscons, _) = missingConsInBranch info brs
               (bs, qss, brs')      = unzip3
                 (map (\(ABranch p exp) -> let (b, qs, e'') = inf exp
                                           in (b, qs, ABranch p e'')) brs)
               canFail              = or bs || not (null misscons)
               qs'                  = concat qss
               e'                   = case mdecl of
                 Just (Type tqn _ vs cs) -> ACase boolType ct e
                   (map addStarVars2Branch (brs' ++ newBrs))
                  where
                   newBrs          = map c2br misscons

                   c2br c = ABranch (patGen c) (boolExpr "False")

                   cqnts           = map (\(Cons qn _ _ ts) -> (qn, ts)) cs

                   consType        = annExpr e --TCons tqn (map (TVar . fst) vs) -- TODO: Specialize type?

                   patGen (qn, ar) = APattern consType (qn, consType)
                     (zip [1 .. ar] (fromMaybe [] (lookup qn cqnts)))
                 Nothing -> ACase boolType Rigid e brs -- TODO: Literal cases
                 _ -> error "Something went wrong" -- Should not happen
               ite                  = ACase boolType Rigid (starVarExp e)
                 [ ABranch (boolPat "True") e'
                 , ABranch (boolPat "False") (boolExpr "False")
                 ]
               boolPat str = APattern boolType (("Prelude", str), boolType) []
           in (canFail, qs', ite)
         ATyped _ e ty' -> let (b, qs, e') = inf e
                           in (b, qs, ATyped boolType e' ty')
         AFree _ vars e -> let (b, qs, e') = inf e
                           in (b, qs, AFree boolType vars e')

addStarVars2Branch :: TABranchExpr -> TABranchExpr
addStarVars2Branch (ABranch p e) = case p of
  APattern _ _ vars@(_ : _) -> ABranch p
    (ALet (annExpr e) (zip (zip (map (starVar . fst) vars) (repeat boolType))
                       (repeat (boolExpr "True"))) e)
  _ -> ABranch p e

addConsts :: TypeExpr -> TAExpr -> TAExpr
addConsts ty e = case ty of
  FuncType t1 t2 -> AComb (FuncType t1 (annExpr e')) FuncCall
    (("Prelude", "const"), constType) [e']
   where
    e'        = addConsts t2 e

    constType = FuncType (TVar 0) (FuncType (TVar 1) (TVar 0))
  ForallType _ t -> addConsts t e
  _ -> e

type Arity = Int

type Constructor = (QName, Arity)

type ModuleName = String

boolExpr :: String -> TAExpr
boolExpr cons = AComb boolType ConsCall (("Prelude", cons), boolType) []

showQNameAsFun :: QName -> String
showQNameAsFun (mod, fun) = mod ++ toUpper c : cs
 where
  (c : cs) = encodeSpecialChars fun

boolType :: TypeExpr
boolType = TCons ("Prelude", "Bool") []

-- Splits the constructors (name/arity) which are missing in the given
-- branches of a case construct from the ones covered
missingConsInBranch :: ProgInfo (TypeDecl, [Constructor])
                    -> [TABranchExpr]
                    -> (Maybe TypeDecl, [Constructor], [Constructor])
missingConsInBranch _ []
  = error "missingConsInBranch: case with empty branches!"
missingConsInBranch _ (ABranch (ALPattern _ _) _ : _) = (Nothing, [], []) --error "TODO: case with literal pattern"
missingConsInBranch info (ABranch (APattern _ (cons, _) args) _ : brs)
  = let (decl, othercons)  = fromMaybe
          (error
           $ "Sibling constructors of " ++ showQName cons ++ " not found!")
          (lookupProgInfo cons info)
        branchcons         = map (patCons . branchPattern) brs
        (missing, covered) = partition ((`notElem` branchcons) . fst) othercons
    in (Just decl, missing, (cons, length args) : covered)

nonFailType :: TypeExpr -> TypeExpr
nonFailType ty = foldr FuncType boolType
  (replicate (length tys) boolType ++ tys)
 where
  tys = FCG.argTypes ty

-- Information about variables: We either know that a variable
-- has a specific outermost constructor or that is has an outermost
-- constructor not contained in a list of constructor names.
type VarMap = DM.Map VarIndex (Either QName [QName])

unrec :: TAFuncDecl -> TAFuncDecl
unrec decl@(AFunc qn arity vis ty rule) = decl'
 where
  decl' = AFunc qn arity vis ty (unrecRule rule)

  unrecRule (AExternal _ _)          = rule
  unrecRule (ARule typ argVars expr) = ARule typ argVars
    (simplifyExpr (unrecExpr decl DM.empty expr))

unrecExpr :: TAFuncDecl -> VarMap -> TAExpr -> TAExpr
unrecExpr decl@(AFunc fname _ _ _ _) vmap expr
  = let frec = unrecExpr decl vmap
    in case expr of
         AVar _ _ -> expr
         ALit _ _ -> expr
         AComb ty ct qn@(fn, _) es
           | fn == fname -> case constantResult decl vmap es of
             Nothing  -> AComb ty ct qn (map frec es)
             Just exp -> exp
           | otherwise -> AComb ty ct qn (map frec es)
         ALet ty binds e -> ALet ty binds
           (unrecExpr decl (DM.union vmap (binds2VarMap binds)) e)  -- todo: unrec binds
         AFree ty fvars e -> AFree ty fvars (frec e)
         AOr ty e1 e2 -> AOr ty (frec e1) (frec e2)
         ACase ty ct v@(AVar vty i) branches -> ACase ty Rigid v
           (unrecBranches branches [])
          where
           unrecBranches :: [TABranchExpr] -> [QName] -> [TABranchExpr]
           unrecBranches [] _ = []
           unrecBranches (ABranch (APattern typ (qn, qty) vs) e : brs) qns
             = ABranch pat e' : unrecBranches brs (qn : qns)
            where
             pat = APattern typ (qn, qty) vs

             e' = unrecExpr decl vmap' e

             vmap' = DM.insertWith upd i (Left qn) vmap

             upd _ new@(Left _)          = new
             upd (Right qs1) (Right qs2) = Right (qs1 ++ qs2)
             upd old@(Left _) (Right _)  = old
           unrecBranches (ABranch p@(ALPattern _ _) e : brs) qns
             = ABranch p (unrecExpr decl vmap e) : unrecBranches brs qns
         ACase ty ct e branches -> ACase ty ct (frec e)
           (map (\(ABranch p exp) -> ABranch p (frec exp)) branches)
         ATyped ty e typ -> ATyped ty (frec e) typ

binds2VarMap :: [((VarIndex, TypeExpr), TAExpr)] -> VarMap
binds2VarMap []                   = DM.empty
binds2VarMap (((i, typ), e) : bs) = case e of
  AComb _ ConsCall (qn, _) _ -> DM.insert i (Left qn) (binds2VarMap bs)
  _ -> binds2VarMap bs

constantResult :: TAFuncDecl -> VarMap -> [TAExpr] -> Maybe TAExpr
constantResult decl@(AFunc qn arity vis ty (ARule rty vars exp)) vmap argExps
  = case go vmap' exp of
    [x] -> Just x
    _   -> Nothing -- todo: no results?
 where
  vmap' = foldr upd DM.empty (zip vars argExps)

  upd ((j, _), e) m = case e of
    AVar _ i -> case DM.lookup i vmap of
      Just x  -> DM.insert j x m
      Nothing -> m
    _        ->
      error $ "Inference.constantResult: normalization failure for " ++ show e

  go :: VarMap -> TAExpr -> [TAExpr]
  go vm e = case e of
    AVar _ i -> case DM.lookup i vm of
      Just x  -> case x of
        Left qn   -> case qn of
          ("Prelude", "True")  -> [boolExpr "True"]
          ("Prelude", "False") -> [boolExpr "False"]
          _                    -> error
            $ "Inference.constantResult.go: Unknown constructor " ++ show qn
        Right qns -> error
          $ "Inference.constantResult.go: Missing constructor for variable "
          ++ show i
      Nothing -> error
        $ "Inference.constantResult.go: Missing binding for variable "
        ++ show i
    ALit _ _ -> [] -- todo: literals
    AComb _ _ (("Prelude", "True"), _) [] -> [boolExpr "True"]
    AComb _ _ (("Prelude", "False"), _) [] -> [boolExpr "False"]
    AComb _ _ _ _ -> [] -- todo: function calls
    ALet _ binds expr -> go (DM.union vm (binds2VarMap binds)) expr
    AFree _ binds expr -> go vm expr -- todo: binds
    AOr _ e1 e2 -> go vm e1 ++ go vm e2
    ACase _ _ (AVar _ i) branches -> case DM.lookup i vm of
      Just x  -> case x of
        Left qn   -> selectBranchExprs qn branches
        Right qns -> removeBranchExprs qns branches
      Nothing -> concatMap (\(ABranch _ e) -> go vm e) branches
     where
      selectBranchExprs :: QName -> [TABranchExpr] -> [TAExpr]
      selectBranchExprs qname brs = concatMap (go vm) $ mapMaybe match brs
       where
        match (ABranch (APattern _ (pqn, _) _) e) | pqn == qname = Just e
                                                  | otherwise = Nothing

      removeBranchExprs :: [QName] -> [TABranchExpr] -> [TAExpr]
      removeBranchExprs qns brs = concatMap (go vm) $ mapMaybe match brs
       where
        match (ABranch (APattern _ (pqn, _) _) e) | pqn `elem` qns = Nothing
                                                  | otherwise = Just e
    ATyped _ e _ -> go vm e

debug f = putStrLn
  $ showFuncDeclAsFlatCurry
  $ unAnnFuncDecl
  $ unrec (snd $ flattenFunc [42 ..] f)