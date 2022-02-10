-----------------------------------------------------------------------------
--- A tool to verify non-failure properties and to check contracts of Curry
--- operations.
---
--- @author  Michael Hanus
--- @version February 2022
---------------------------------------------------------------------------

module Main where

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
   bannerText = "Property Verification Tool for Curry (Version of 10/02/22)"
   bannerLine = take (length bannerText) (repeat '=')

---------------------------------------------------------------------------
main :: IO ()
main = do
  args <- getArgs
  (opts,progs) <- processOptions banner args
  let optname = optName opts
  if not (null optname)
    then putStrLn $ "Non-failure condition for '" ++ optname ++ "':\n" ++
                    encodeContractName (optname ++ "'nonfail")
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
  prog <- readSimpTypedFlatCurryWithSpec modname
  let errs = checkContractUsage (progName prog)
               (map (\fd -> (snd (funcName fd), funcType fd)) (progFuncs prog))
  unless (null errs) $ lift $ do
    putStr $ unlines (map showOpError errs)
    exitWith 1
  impprogs <- mapM readSimpTypedFlatCurryWithSpec $ progImports prog
  let allprogs = prog : impprogs
  addProgsToState allprogs
  addFunsToVerifyInfo $ concatMap progFuncs allprogs
  pi1 <- lift getProcessInfos
  printWhenAll $ unlines $
    ["ORIGINAL PROGRAM:", line, showCurryModule (unAnnProg prog), line]
  whenOption optFailfree $ proveNonFailingFuncs prog
  evalOption optContract (> 0) $ do
    modifyOptions (\opts -> opts { optConFail = True })
    prog' <- verifyPostConditions prog >>= verifyPreConditions
    whenOption optWrite $ do
      prog'' <- addPreConditions prog'
      lift $ do
        ccprog <- fromJust <$>
          readTypedFlatCurryFromPath "include" "ContractChecker"
        let ccfuncs  = map (updFuncName $ \n -> (modname, snd n)) $
                           progFuncs ccprog
            prog'''  = updProgFuncs (++ ccfuncs) prog''
        writeFlatCurry $ unAnnProg prog'''
        writeTypeAnnotatedFlatCurry prog'''
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


Verified system libraries:

- Prelude
- Char
- Either
- ErrorState
- Integer
- Maybe
- State
- ShowS

 Prelude Char Either ErrorState Integer Maybe State ShowS

-}
