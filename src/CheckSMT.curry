module CheckSMT
  ( checkNonFailFunc, checkPreCon, checkPostCon
  ) where

import Control.Monad               ( unless )
import Control.Monad.IO.Class      ( liftIO )
import Control.Monad.Trans.Class   ( lift )
import Control.Monad.Trans.State   ( gets )
import Data.List                   ( find, intercalate, union, partition )
import Data.Maybe                  ( catMaybes, fromJust, mapMaybe )
import Solver.SMTLIB.Z3
import System.Directory            ( removeFile )
import System.IO                   ( hClose, hGetContents )
import System.IOExts               ( execCmd )

import Contract.Names              ( toPreCondName, toPreCondQName
                                   , toPostCondName, toPostCondQName )
import FlatCurry.Annotated.Goodies
import FlatCurry.Annotated.Pretty  ( ppTypeExp, ppQName )
import FlatCurry.Types             ( showQName )
import Language.SMTLIB.Goodies
import Language.SMTLIB.Pretty
import qualified Language.SMTLIB.Types as SMT
import Text.Pretty                 ( hsep, pPrint, pretty )

import Curry2SMT
import ESMT
import FlatCurry.Typed.Build
import FlatCurry.Typed.Names
import FlatCurry.Typed.Read        ( stripForall )
import FlatCurry.Typed.Types
import ToolOptions
import TransState
import VerifierState

---------------------------------------------------------------------------
-- Checks the satisfiability of the given assertion and checks the fail
-- condition if the assertion is satisfiable.
checkNonFailFunc :: String -> SMT.Term -> SMT.Term -> SMT.Term
                 -> TransStateM (Maybe Bool)
checkNonFailFunc scripttitle assertion impbindings imp =
  generateSMT scripttitle assertion impbindings imp
    >>= checkSMT evalNonFailFunc []
      (\name args _ -> "Call" ++ printCall name args ++ "fails")

-- Checks the satisfiability of the given assertion and checks the pre
-- condition if the assertion is satisfiable.
checkPreCon :: String -> SMT.Term -> SMT.Term -> SMT.Term -> String -> [Int]
            -> TransStateM (Maybe Bool)
checkPreCon scripttitle assertion impbindings imp mname mvars = do
  optcontract <- lift $ getOption optContract
  if optcontract > 1
    then
      generateSMT scripttitle assertion impbindings imp
        >>= checkSMT evalPreCon mvars (\name args margs -> "Call"
          ++ printCall mname margs ++ "violates " ++ toPreCondName name
          ++ " due to calling" ++ printCall name args)
    else return $ Just False

-- Checks the satisfiability of the given assertion and checks the post
-- condition if the assertion is satisfiable.
checkPostCon :: String -> SMT.Term -> SMT.Term -> SMT.Term
             -> TransStateM (Maybe Bool)
checkPostCon scripttitle assertion impbindings imp = do
  optcontract <- lift $ getOption optContract
  if optcontract > 1
    then
      generateSMT scripttitle assertion impbindings imp
        >>= checkSMT evalPostCon [] (\name args _ -> "Call"
          ++ printCall name args ++ "violates " ++ toPostCondName name)
    else return $ Just False

-- Generates a string representation of a function call.
printCall :: String -> [String] -> String
printCall name args = " '" ++ name ++ [' ' | not $ null args]
                          ++ unwords args ++ "' "

---------------------------------------------------------------------------
-- Generates a SMT script from the given assertion.
generateSMT :: String -> SMT.Term -> SMT.Term -> SMT.Term
            -> TransStateM ([SMT.Command])
generateSMT scripttitle assertion impbindings imp = do
  vartypes <- getVarTypes
  let (pretypes,usertypes) =
         partition ((== "Prelude") . fst)
                  (foldr union []
                    (map (tconsOfTypeExpr . (\(_,x,_) -> x)) vartypes))
      allsyms = catMaybes
                  (map (\n -> maybe Nothing Just (untransOpName n))
                       (map unqual
                         (allQIdsOfTerm (tand [assertion, impbindings, imp]))))
  unless (null allsyms) $ lift $ printWhenIntermediate $
    "Translating operations into SMT: " ++
    unwords (map showQName allsyms)
  smtfuncs <- lift $ funcs2SMT allsyms
  tdecls   <- mapM (lift . tdeclOf) usertypes
  let decls = map (maybe (error "Internal error: some datatype not found!") id)
                  tdecls
      smt1  = [ SMT.Comment scripttitle ] ++
              prelude ++
              concatMap preludeType2SMT (map snd pretypes) ++
              (if null decls
                 then []
                 else [ SMT.Comment "User-defined datatypes:" ] ++
                      map tdecl2SMT decls)
      smt2  = [ SMT.Comment "Free variables:" ] ++
              concatMap typedVar2SMT vartypes ++
              [ SMT.Comment "Boolean formula of assertion (known properties):"
              , sAssert assertion
              , SMT.Comment "Bindings of implication:"
              , sAssert impbindings
              , SMT.Comment "Assert negated implication:"
              , sAssert (tnot imp)
              ]
      smt   = unpoly $ (map Right smt1) ++ [Left smtfuncs] ++ (map Right smt2)
  lift $ printWhenAll $
    "SMT SCRIPT:\n" ++ (showWithLineNums $ showSMT $ smt ++
    [ SMT.Comment "check satisfiability:"
    , SMT.CheckSat
    , SMT.Comment "if unsat, the implication is valid"
    ])
  return smt

-- Checks the given SMT script for satisfiability and evaluates the returned
-- values with the given evaluation function if the solver returns satisfiable.
checkSMT :: (QName -> TypeExpr -> [[String]] -> IO [Bool]) -> [Int]
         -> (String -> [String] -> [String] -> String) -> [SMT.Command]
         -> TransStateM (Maybe Bool)
checkSMT eval mvars output smt = do
  vartypes <- getVarTypes
  let getvaluevars =
        mapMaybe
          (\(i, vartype, mn) -> case mn of
            Just (name, pos, funcindex) | pos /= 0 && funcindex /= 0 ->
              Just (tvar i, ((name, funcindex), vartype))
            _ -> Nothing
          )
          vartypes
      argtypes = groupPairs $ map snd getvaluevars
      mvars' = map tvar mvars
  lift $ printWhenAll $ "CALLING Z3 (with options: -smt2 -T:5)..."
  exNum <- lift $ getOption optExamples
  answer <- liftIO $
    evalSessions z3 { flags = ["-smt2", "-in", "-T:5"] } defSMTOpts $
      solveAllSMTVars (union mvars' $ map fst getvaluevars) smt exNum
  case answer of
    Left  errs -> (lift $ printWhenAll $ pPrint $ hsep $ map pretty errs) >>
                  return Nothing
    Right vpss -> if null vpss
      then (lift $ printWhenAll "RESULT:\nunsat") >> return (Just True)
      else do
        lift $ printWhenAll "RESULT:\nsat"
        let mres = map (map (decodeTerm . snd) . filter ((`elem` mvars') . fst))
                   vpss
        allfuncs <- lift $ gets $ allFuncs . trInfo
        counterExamples <- liftIO $ checkFuncs eval allfuncs argtypes
          $ map (\(f, args) -> (f, zip args mres))
          $ groupPairs $ concatMap
              (groupPairs . (mapMaybe (\(var, val) ->
                (,) <$> (fst <$> lookup var getvaluevars)
                    <*> Just (decodeTerm val))))
              vpss
        lift $ printWhenStatus $ unlines $ map
          (\(name, args) -> unlines $ map
            (\(arg, marg) -> output name arg marg) args) counterExamples
        return $ Just False

-- SMT script for declaring Prelude datatypes.
prelude :: [SMT.Command]
prelude =
  [ SMT.Comment "disable model-based quantifier instantiation (avoid loops)"
  , SMT.SetOption $ SMT.OptAttr $ SMT.AVal (SMT.KW "smt.mbqi")
                                           (SMT.AVSym "false")
  , SMT.Comment "For polymorphic types:"
  , SMT.DeclareSort "TVar" 0
  , SMT.Comment "Unit type:"
  , SMT.DeclareDatatype "Unit" $ SMT.MT [SMT.Cons "unit" []]
  , SMT.Comment "Pair type:"
  , SMT.DeclareDatatype "Pair" $
      SMT.PT ["T1", "T2"]
             [ SMT.Cons "mk-pair"
                        [ SMT.SV "first"  $ SMT.SComb "T1" []
                        , SMT.SV "second" $ SMT.SComb "T2" []
                        ]
             ]
  , SMT.Comment "For functional types:"
  , SMT.DeclareDatatype "Func" $
      SMT.PT ["T1", "T2"]
             [ SMT.Cons "mk-func"
                        [ SMT.SV "argument" $ SMT.SComb "T1" []
                        , SMT.SV "result"   $ SMT.SComb "T2" []
                        ]
             ]
  , SMT.Comment "Maybe type:"
  , SMT.DeclareDatatype "Maybe" $
      SMT.PT ["T"]
             [ SMT.Cons "Nothing" []
             , SMT.Cons "Just" [SMT.SV "just" $ SMT.SComb "T" []]
             ]
  , SMT.Comment "Either type:"
  , SMT.DeclareDatatype "Either" $
      SMT.PT ["T1", "T2"]
             [ SMT.Cons "Left"  [SMT.SV "left"  $ SMT.SComb "T1" []]
             , SMT.Cons "Right" [SMT.SV "right" $ SMT.SComb "T2" []]
             ]
  , SMT.Comment "Ordering type:"
  , SMT.DeclareDatatype "Ordering" $
      SMT.MT [SMT.Cons "LT" [], SMT.Cons "EQ" [], SMT.Cons "GT" []]
  , SMT.Comment "Dict type (to represent dictionary variables):"
  , SMT.DeclareDatatype "Dict" $
      SMT.PT ["T"] [SMT.Cons "Dict" [SMT.SV "dict" $ SMT.SComb "T" []]]
  ]

---------------------------------------------------------------------------
-- Decodes a SMT term into a string representation of a Curry term.
decodeTerm :: SMT.Term -> String
decodeTerm (SMT.TConst tconst) = case tconst of
                                   SMT.Num num -> negParen num
                                   SMT.Dec dec -> negParen dec
                                   SMT.Str str -> "'" ++ str ++ "'"
  where
    negParen n = if n < 0 then "(" ++ show n ++ ")" else show n
decodeTerm (SMT.TComb qIdent terms) =
  paren $ decodeIdent qIdent ++ [' ' | not $ null terms]
          ++ (unwords $ map decodeTerm terms)
  where
    paren s = if null terms then s else "(" ++ s ++ ")"
    decodeIdent (SMT.Id ident)   = decodeIdent' ident
    decodeIdent (SMT.As ident _) = decodeIdent' ident
    decodeIdent' ident           =
      case lookup ident $ map (\(x,y) -> (y,x)) transPrimCons of
        Just ":"    -> "(:)"
        Just ident' -> ident'
        Nothing     -> let (modname, ident') = break (== '_') ident in
                         modname ++ (if null modname then "" else ".")
                         ++ dropWhile (== '_') ident'
decodeTerm (SMT.Let decls term) =
  "(let {"
  ++ intercalate "; " (map (\(sym, t) -> sym ++ " = " ++ decodeTerm t) decls)
  ++ "} in " ++ decodeTerm term ++ ")"
decodeTerm (SMT.Forall _ term) = decodeTerm term
decodeTerm (SMT.Exists _ term) = decodeTerm term
decodeTerm (SMT.Match term pats) =
  "case " ++ decodeTerm term ++ " of {"
  ++ intercalate "; " (map decodeBranch pats) ++ "}"
  where
    decodeBranch ((SMT.PComb cons args), branch) =
      cons ++ " " ++ unwords args ++ " -> " ++ decodeTerm branch
decodeTerm (SMT.Annot term _) = decodeTerm term

-- Check if the given functions fail with their given arguments and return only
-- those that do.
checkFuncs :: (QName -> TypeExpr -> [[String]] -> IO [Bool])
           -> [TAFuncDecl] -> [((QName, Int), [TypeExpr])]
           -> [((QName, Int), [([String], [String])])]
           -> IO [(String, [([String], [String])])]
checkFuncs _ _     _           []                        = return []
checkFuncs eval funcs argtypes ((fn@(qn, _), args) : fs) = do
  let ftype = funcType $ fromJust $ find (\f -> funcName f == qn) funcs
      sub = concatMap (uncurry matchTypeVars)
            $ zip (argTypes ftype) $ fromJust $ lookup fn argtypes
      ftype' = updTVars (const $ TCons ("Prelude", "()") [])
               $ updTVars (\i -> fromJust $ lookup i sub) $ resultType ftype
  results <- eval qn ftype' $ map fst args
  let args' = mapMaybe
                (\(r, arg) -> if not r then Just arg else Nothing)
                $ zip results args
  if null args'
    then checkFuncs eval funcs argtypes fs
    else checkFuncs eval funcs argtypes fs
           >>= \fs' -> return $ (snd qn, args') : fs'

-- Matches the first argument with the second and returns the corresponding
-- type expression for each type variable in the first argument.
matchTypeVars :: TypeExpr -> TypeExpr -> [(TVarIndex, TypeExpr)]
matchTypeVars (TVar i) texpr = [(i, stripForall texpr)]
matchTypeVars (FuncType arg res) texpr = case stripForall texpr of
  FuncType arg' res' -> union (matchTypeVars arg arg') (matchTypeVars res res')
  _                  -> error "CheckSMT.matchTypeVars: unexpected case"
matchTypeVars (TCons qn args) texpr = case stripForall texpr of
  TCons qn' args' | qn == qn' -> foldr union [] $
                                   map (uncurry matchTypeVars) $ zip args args'
  _                           -> error "CheckSMT.matchTypeVars: unexpected case"
matchTypeVars (ForallType _ texp) texp' = matchTypeVars texp texp'

---------------------------------------------------------------------------
-- Evaluate the given function with `getAllValues` and returns `False` for each
-- argument for which the function fails.
evalNonFailFunc :: QName -> TypeExpr -> [[String]] -> IO [Bool]
evalNonFailFunc funcname functype args =
  evalFunc False funcname functype args >>= return . map (/= "[]")

-- Evaluate the precondition for the given function with `getAllValues` and
-- return if it holds for the given arguments.
evalPreCon :: QName -> TypeExpr -> [[String]] -> IO [Bool]
evalPreCon funcname _ args =
  evalFunc False (toPreCondQName funcname) boolType args
    >>= return . map (((&&) <$> and <*> not . null) . read)

-- Evaluate the given function with `getAllValues` and then evaluate if the
-- postcondition holds for all possible results.
evalPostCon :: QName -> TypeExpr -> [[String]] -> IO [Bool]
evalPostCon funcname functype args = do
  evalFunc True funcname functype args
    >>= return . map (((&&) <$> and <*> not . null) . read)

-- Evaluate a function with `getAllValues` and return the output of the
-- compiler.
-- The first argument controls if functions for checking post conditons should
-- be generated.
evalFunc :: Bool -> QName -> TypeExpr -> [[String]] -> IO [String]
evalFunc post funcname functype args = do
  let functype' = ioType $ listType functype
  writeFile "Eval.curry" $ unlines $
    [ "module Eval where"
    , "import Control.AllValues ( getAllValues )"
    , "import " ++ fst funcname
    , "eval :: IO ()"
    , "eval = sequence_ ["
      ++ (intercalate ", " $ map (\i -> "eval" ++ (if post then "Post" else "")
                                        ++ show i ++ " >>= print")
                                 [1..length args]) ++ "]"
    ] ++ map (\(i, arg) -> "eval" ++ show i ++ " :: "
                           ++ pPrint (ppTypeExp functype')
                           ++ "\neval" ++ show i ++ " = getAllValues ("
                           ++ pPrint (ppQName funcname) ++ " " ++ unwords arg
                           ++ ")"
                           ++ (if post then
                                 "\nevalPost" ++ show i ++ " :: IO [Bool]\n"
                                 ++ "evalPost" ++ show i ++ " = eval" ++ show i
                                 ++ " >>= mapM (getAllValues . "
                                 ++ pPrint (ppQName $ toPostCondQName funcname)
                                 ++ " " ++ unwords arg ++ ") >>= return . map "
                                 ++ "((&&) <$> and <*> not . null)"
                               else ""
                              )
             ) (zip [1..] args)
  (i,o,e) <- execCmd "curry -q :l Eval :eval eval :quit"
  hClose i
  hGetContents e >>= putStrLn
  out <- hGetContents o
  removeFile "Eval.curry"
  return $ lines out

---------------------------------------------------------------------------
-- Translate a typed variables to an SMT declaration:
typedVar2SMT :: (Int,TypeExpr, Maybe (QName, Int, Int)) -> [SMT.Command]
typedVar2SMT (i, te, Just (name, argPos, _)) =
  [ SMT.Comment $
      (case argPos of
        0 -> "result"
        _ -> show argPos
             ++ (case argPos of {1 -> "st"; 2 -> "nd"; 3 -> "rd"; _ -> "th"})
             ++ " argument")
      ++ " of '" ++ snd name ++ "'"
  , SMT.DeclareConst (var2SMT i) (polytype2sort te)
  ]
typedVar2SMT (i, te, Nothing) =
  [SMT.DeclareConst (var2SMT i) (polytype2sort te)]

-- Gets all type constructors of a type expression.
tconsOfTypeExpr :: TypeExpr -> [QName]
tconsOfTypeExpr (TVar _) = []
tconsOfTypeExpr (FuncType a b) =  union (tconsOfTypeExpr a) (tconsOfTypeExpr b)
tconsOfTypeExpr (TCons qName texps) =
  foldr union [qName] (map tconsOfTypeExpr texps)
tconsOfTypeExpr (ForallType _ te) =  tconsOfTypeExpr te

-- Group a list of pairs together according to the first component.
groupPairs :: Eq a => [(a, b)] -> [(a, [b])]
groupPairs xs = foldr groupPairs' [] (map fst xs)
  where
    -- groupPairs' :: Eq a => a -> [(a, [b])] -> [(a, [b])]
    groupPairs' x xs' | x `elem` (map fst xs') = xs'
                      | otherwise              = (x, findElems x) : xs'

    -- findElems :: Eq a => a -> [b]
    findElems x' = map snd $ filter ((== x') . fst) xs

---------------------------------------------------------------------------
--- Shows a text with line numbers prefixed:
showWithLineNums :: String -> String
showWithLineNums txt =
  let txtlines  = lines txt
      maxlog    = ilog (length txtlines + 1)
      showNum n = (take (maxlog - ilog n) (repeat ' ')) ++ show n ++ ": "
  in unlines . map (uncurry (++)) . zip (map showNum [1..]) $ txtlines

--- The value of `ilog n` is the floor of the logarithm
--- in the base 10 of `n`.
--- Fails if `n &lt;= 0`.
--- For positive integers, the returned value is
--- 1 less the number of digits in the decimal representation of `n`.
---
--- @param n - The argument.
--- @return the floor of the logarithm in the base 10 of `n`.
ilog :: Int -> Int
ilog n | n>0 = if n<10 then 0 else 1 + ilog (n `div` 10)
