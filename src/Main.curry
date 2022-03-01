-----------------------------------------------------------------------------
--- A tool to verify non-failure properties and to check contracts of Curry
--- operations.
---
--- @author  Michael Hanus
--- @version February 2022
---------------------------------------------------------------------------

module Main where

import Analysis.TotallyDefined     ( siblingConsAndDecl )
import Control.Monad               ( unless, when )
import Control.Monad.Trans.Class   ( lift )
import Control.Monad.Trans.State   ( evalStateT, get, gets )
import Data.List                   ( (\\) )
import Data.Maybe                  ( fromJust )
import System.Environment          ( getArgs )
import System.FilePath             ( (</>) )
import System.Path                 ( fileInPath )
import System.Process              ( exitWith )

import Contract.Names              ( encodeContractName )
import Contract.Usage              ( checkContractUsage )
import Debug.Profile               ( ProcessInfo(ElapsedTime), getProcessInfos )
import FlatCurry.Annotated.Goodies
import FlatCurry.Files             ( readFlatCurryInt, writeFlatCurry )
import FlatCurry.ShowIntMod        ( showCurryModule )
import FlatCurry.TypeAnnotated.Files ( readTypeAnnotatedFlatCurry
                                     , writeTypeAnnotatedFlatCurry )
import FlatCurry.Types             ( Prog(Prog) )
import FlatCurry.Typed.Simplify    ( simpProg )


import ContractProver
import Failfree
import FlatCurry.Typed.Read
import PackageConfig ( packagePath )
import ToolOptions
import VerifierState
------------------------------------------------------------------------
-- To support testing:

test :: Int -> String -> IO ()
test v s = evalStateT (verifyMod s) $
             initVState $ defaultOptions { optVerb = v }

testv :: String -> IO ()
testv = test 3

testcv :: String -> IO ()
testcv s = evalStateT (verifyMod s) $
           initVState $ defaultOptions { optVerb = 3, optConFail = True }

------------------------------------------------------------------------

banner :: String
banner = unlines [bannerLine,bannerText,bannerLine]
 where
   bannerText = "Property Verification Tool for Curry (Version of 11/02/22)"
   bannerLine = take (length bannerText) (repeat '=')

---------------------------------------------------------------------------
main :: IO ()
main = do
  args <- getArgs
  (opts,progs) <- processOptions banner args
  let optname = optName opts
  if not (null optname)
    then putStrLn $ showEncodedNames optname
    else do
      z3exists <- fileInPath "z3"
      if z3exists
        then do
          when (optVerb opts > 0) $ putStrLn banner
          evalStateT (verifyModules [] progs) (initVState opts)
        else do
          putStrLn "PROPERTY VERIFICATION SKIPPED:"
          putStrLn "The SMT solver Z3 is required for the verifier to work"
          putStrLn "but the program 'z3' is not found on the PATH!"
          exitWith 1

-- Shows the names of a non-fail condition and pre-/postconditions for
-- a given identifier (typically, operators with special characters).
showEncodedNames :: String -> String
showEncodedNames cid = unlines
  [ "Names to specify properties of operation '" ++ cid ++ "':"
  , "Non-fail condition: " ++ encodeContractName (cid ++ "'nonfail")
  , "Precondition:       " ++ encodeContractName (cid ++ "'pre")
  , "Postcondition:      " ++ encodeContractName (cid ++ "'post")
  ]

verifyModules :: [String] -> [String] -> VStateM ()
verifyModules _            []           = return ()
verifyModules verifiedmods (mod : mods)
  | mod `elem` verifiedmods = verifyModules verifiedmods mods
  | otherwise = do
      isRec <- getOption optRec
      if isRec
        then do
          (Prog _ imps _ _ _) <- lift $ readFlatCurryInt mod
          let newimps = filter (`notElem` verifiedmods) imps
          if null newimps
            then do
              printWhenStatus ""
              verifyMod mod
              verifyModules (mod : verifiedmods) mods
            else
              verifyModules verifiedmods $ newimps ++ mod : (mods \\ newimps)
        else do
          verifyMod mod
          verifyModules (mod : verifiedmods) mods

verifyMod :: String -> VStateM ()
verifyMod modname = do
  printWhenStatus $ "Analyzing module '" ++ modname ++ "':"
  oprog <- readTypedFlatCurryWithSpec modname
  let errs = checkContractUsage (progName oprog)
               (map (\fd -> (snd (funcName fd), funcType fd)) (progFuncs oprog))
  unless (null errs) $ lift $ do
    putStr $ unlines (map showOpError errs)
    exitWith 1
  let prog = simpProg oprog
  failfree <- getOption optFailfree
  impprogs <- if failfree
                then mapM readSimpTypedFlatCurryWithSpec $ progImports prog
                else return []
  let allprogs = prog : impprogs
  addProgsToState allprogs
  addFunsToVerifyInfo $ concatMap progFuncs allprogs
  whenOption optInferNFCs $ do
    siblingconsinfo <- lift $ loadAnalysisWithImports siblingConsAndDecl prog
    inferNFCs modname siblingconsinfo
  pi1 <- lift getProcessInfos
  printWhenAll $ unlines $
    ["ORIGINAL PROGRAM:",   line, showCurryModule (unAnnProg oprog), line,
     "SIMPLIFIED PROGRAM:", line, showCurryModule (unAnnProg prog),  line]
  whenOption optFailfree $ proveNonFailingFuncs prog
  evalOption optContract (> 0) $ do
    modifyOptions (\opts -> opts { optConFail = True })
    prog1 <- verifyPostConditions oprog >>= verifyPreConditions
    whenOption (\o -> optFCY o || optAFCY o) $ do
      prog2 <- addPreConditions prog1
      tprog <- lift $ do
        ccprog <- fromJust <$>
          readTypedFlatCurryFromPath "include" "ContractChecks"
        let ccfuncs = progFuncs (rnmProg modname ccprog)
        return $ updProgFuncs (++ ccfuncs) prog2
      printWhenAll $ unlines $
        ["TRANSFORMED PROGRAM WITH CONTRACT CHECKING:", line,
         showCurryModule (unAnnProg tprog), line]
      whenOption optFCY  $ lift $ writeFlatCurry $ unAnnProg tprog
      whenOption optAFCY $ lift $ writeTypeAnnotatedFlatCurry tprog
  pi2 <- lift $ getProcessInfos
  let tdiff = maybe 0 id (lookup ElapsedTime pi2) -
              maybe 0 id (lookup ElapsedTime pi1)
  whenOption optTime $ lift $ putStrLn $
    "TOTAL VERIFICATION TIME  : " ++ show tdiff ++ " msec"
  showStats
 where
  line = take 78 (repeat '-')

  showOpError (qf,err) =
    snd qf ++ " (module " ++ fst qf ++ "): " ++ err

---------------------------------------------------------------------------
-- Operations axiomatized by specific smt scripts (no longer necessary
-- since these scripts are now automatically generated by Curry2SMT.funcs2SMT).
-- However, for future work, it might be reasonable to cache these scripts
-- for faster contract checking.
axiomatizedOps :: [String]
axiomatizedOps = ["Prelude_null","Prelude_take","Prelude_length"]

---------------------------------------------------------------------------

{-

Still to be done:

- consider encapsulated search

-}
