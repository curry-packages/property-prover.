module VerifierState where

import Analysis.ProgInfo
import Control.Applicative         ( when )
import Control.Monad.Trans.Class   ( lift )
import Control.Monad.Trans.State   ( StateT, get, gets, modify, put )
import Data.List                   ( find, isSuffixOf, nub )

import Contract.Names              ( isNonFailName, isPreCondName
                                   , isPostCondName )
import FlatCurry.Annotated.Goodies
import FlatCurry.ShowIntMod        ( showFuncDeclAsFlatCurry )

import FlatCurry.Typed.TypeCheck
import FlatCurry.Typed.Types
import ToolOptions
import Inference.Inference


---------------------------------------------------------------------------
-- Some global information used by the verification process:
data VerifyInfo = VerifyInfo
  { toolOpts      :: Options      -- options passed to the tool
  , allFuncs      :: [TAFuncDecl] -- all defined operations
  , preConds      :: [TAFuncDecl] -- all precondition operations
  , postConds     :: [TAFuncDecl] -- all postcondition operations
  , nfConds       :: [TAFuncDecl] -- all non-failure condition operations
  }

initVerifyInfo :: Options -> VerifyInfo
initVerifyInfo opts = VerifyInfo opts [] [] [] []

addFunsToVerifyInfo' :: [TAFuncDecl] -> VerifyInfo -> VerifyInfo
addFunsToVerifyInfo' fdecls ti =
  ti { allFuncs  = fdecls    ++ allFuncs  ti
     , preConds  = preconds  ++ preConds  ti
     , postConds = postconds ++ postConds ti
     , nfConds   = nfconds   ++ nfConds   ti
     }
 where
  -- Precondition operations:
  preconds  = filter (isPreCondName  . snd . funcName) fdecls
  -- Postcondition operations:
  postconds = filter (isPostCondName . snd . funcName) fdecls
  -- Non-failure condition operations:
  nfconds   = filter (isNonFailName  . snd . funcName) fdecls

inferNFCs :: String -> ProgInfo (TypeDecl, [Constructor]) -> VStateM ()
inferNFCs modname pinfo = do
  vstate <- get
  let infconds = nub (inferNFConds modname pinfo (allFuncs ti))
      ti = trInfo vstate
      ti'      = ti
        { allFuncs = allFuncs ti ++ infconds -- TODO: remove duplicate NFCs
        , nfConds  = nfConds ti ++ infconds
        }
      line = replicate 78 '-'
  put vstate { trInfo = ti' }
  addNFCsToProgs infconds
  printWhenAll 
    $ unlines
    $ ["INFERRED NON-FAILURE CONDITIONS:", line]
    ++ map (('\n' :) . showFuncDeclAsFlatCurry . unAnnFuncDecl) infconds
    ++ [line]
  checkProgs

--- Run type check on all programs
checkProgs :: VStateM ()
checkProgs = do
  vstate <- get
  bs <- lift $ mapM (`isSaneProg` True) (currTAProgs vstate)
  lift $ if and bs
            then putStrLn "TYPE CHECK: SUCCESS"
            else putStrLn "TYPE CHECK: FAILURE"
  
--- Adds NFCs to the respective program determined by the qualified name
addNFCsToProgs :: [TAFuncDecl] -> VStateM ()
addNFCsToProgs nfcs = do
  vstate <- get
  let progs = currTAProgs vstate
      addNFC (AProg modname imps tds fds opds) =
        let nfcs' = filter (\nfc -> fst (funcName nfc) == modname) nfcs
        in AProg modname imps tds (fds ++ nfcs') opds
  put (vstate { currTAProgs = map addNFC progs })

--- Is an operation name the name of a contract or similar?
isContractOp :: QName -> Bool
isContractOp (_,fn) = isNonFailName fn || isPreCondName fn || isPostCondName fn

--- Is a function declaration a property?
isProperty :: TAFuncDecl -> Bool
isProperty fdecl =
  resultType (funcType fdecl)
    `elem` map (\tc -> TCons tc [])
               [("Test.Prop","Prop"),("Test.EasyCheck","Prop")]

---------------------------------------------------------------------------
-- The global state of the verification process keeps some
-- statistical information and the programs that are already read (to
-- avoid multiple readings).
data VState = VState
  { trInfo       :: VerifyInfo        -- information used by the verifier
  , failedFuncs  :: [(String,String)] -- partially defined operations
                                      -- and their failing reason
  , numAllFuncs  :: Int               -- number of analyzed operations
  , numNFCFuncs  :: Int               -- number of operations with non-trivial
                                      -- non-failing conditions
  , numPatTests  :: Int               -- number of missing pattern tests
  , numFailTests :: Int               -- number of tests of failure calls
  , uPreCond     :: [String]          -- unverified preconditions
  , vPreCond     :: [String]          -- verified preconditions
  , uPostCond    :: [String]          -- unverified postconditions
  , vPostCond    :: [String]          -- verified postconditions
  , currTAProgs  :: [TAProg]          -- already read typed FlatCurry programs
  }

initVState :: Options -> VState
initVState opts = VState (initVerifyInfo opts) [] 0 0 0 0 [] [] [] [] []

-- The type of the state monad containing the verification state.
type VStateM a = StateT VState IO a

---------------------------------------------------------------------------
-- Modifies the options with the given function.
modifyOptions :: (Options -> Options) -> VStateM ()
modifyOptions f = do
  vstate <- get
  let vinfo  = trInfo vstate
      vinfo' = vinfo { toolOpts = f $ toolOpts vinfo}
  put vstate { trInfo = vinfo' }

-- Gets a specific option.
getOption :: (Options -> a) -> VStateM a
getOption f = gets (toolOpts . trInfo) >>= return . f

-- Gets an option and only executes the given monad if the given predicate
-- evaluates to true for that option.
evalOption :: (Options -> a) -> (a -> Bool) -> VStateM () -> VStateM ()
evalOption f b m = getOption f >>= flip when m . b

-- Gets an option and only executes the given monad if this option is true.
whenOption :: (Options -> Bool) -> VStateM () -> VStateM ()
whenOption f = evalOption f id

---------------------------------------------------------------------------
printWhenStatus :: String -> VStateM ()
printWhenStatus s = evalOption optVerb (> 0) $ printCP s

printWhenIntermediate :: String -> VStateM ()
printWhenIntermediate s = evalOption optVerb (> 1) $ printCP s

printWhenAll :: String -> VStateM ()
printWhenAll s = evalOption optVerb (> 2) $ printCP s

printCP :: String -> VStateM ()
printCP s = lift $ putStrLn $ "INFO: " ++ s

---------------------------------------------------------------------------
--- Shows the statistics for the failfree verification in human-readable
--- format.
showFailfreeStats :: VState -> String
showFailfreeStats vstate = unlines $
  [ "TESTED OPERATIONS        : " ++ show (numAllFuncs vstate)
  , "NONFAIL CONDITIONS       : " ++ show (numNFCFuncs vstate)
  , "TESTS OF MISSING PATTERNS: " ++ show (numPatTests vstate)
  , "TESTS OF NON-FAIL CALLS  : " ++ show (numFailTests vstate) ] ++
  showStat "POSSIBLY FAILING OPERATIONS" (failedFuncs vstate) ++
  if isVerifiedFailfree vstate
    then ["NON-FAILURE VERIFICATION SUCCESSFUL!"]
    else []
 where
  showStat t fs =
    if null fs
      then []
      else (t ++ ":") :
           map (\ (fn,reason) -> fn ++ " (" ++ reason ++ ")")
               (reverse fs)

--- Shows the statistics for the contract checking in human-readable format.
showContractStats :: VState -> String
showContractStats vstate =
 showStat "PRECONDITIONS : VERIFIED  " (vPreCond  vstate) ++
 showStat "PRECONDITIONS : UNVERIFIED" (uPreCond  vstate) ++
 showStat "POSTCONDITIONS: VERIFIED  " (vPostCond vstate) ++
 showStat "POSTCONDITIONS: UNVERIFIED" (uPostCond vstate) ++
 (if isVerifiedContracts vstate
    then "\nALL CONTRACTS VERIFIED!"
    else "")
 where
  showStat t fs = if null fs then "" else "\n" ++ t ++ ": " ++ unwords fs

--- Shows the statistics in human-readable format.
showStats :: VStateM ()
showStats = do
  vstate <- get
  let opts     = toolOpts $ trInfo vstate
      notQuiet = optVerb opts > 0
  when ((notQuiet || not (isVerifiedFailfree vstate)) && optFailfree opts)
    $ lift $ putStr $ showFailfreeStats vstate
  when ((notQuiet || not (isVerifiedContracts vstate)) && optContract opts > 1)
    $ lift $ putStrLn $ showContractStats vstate

--- Are all non-failing properties verified?
isVerifiedFailfree :: VState -> Bool
isVerifiedFailfree vstate = null (failedFuncs vstate)

--- Are all contracts verified?
isVerifiedContracts :: VState -> Bool
isVerifiedContracts vstate = null (uPreCond vstate) && null (uPostCond vstate)

---------------------------------------------------------------------------
addFunsToVerifyInfo :: [TAFuncDecl] -> VStateM ()
addFunsToVerifyInfo fdecls = do
  ti <- gets trInfo
  modify $ \vstate -> vstate { trInfo = addFunsToVerifyInfo' fdecls ti }

--- Adds a possibly failing call in a functions and the called function.
addFailedFuncToStats :: String -> String -> VStateM ()
addFailedFuncToStats fn qfun =
  modify $ \vstate -> vstate { failedFuncs = (fn,qfun) : failedFuncs vstate }

--- Increments the number of all tested functions.
incNumAllInStats :: VStateM ()
incNumAllInStats =
  modify $ \vstate -> vstate { numAllFuncs = numAllFuncs vstate + 1 }

--- Increments the number of operations with nonfail conditions.
incNumNFCInStats :: VStateM ()
incNumNFCInStats =
  modify $ \vstate -> vstate { numNFCFuncs = numNFCFuncs vstate + 1 }

--- Increments the number of missing pattern tests.
incPatTestInStats :: VStateM ()
incPatTestInStats =
  modify $ \vstate -> vstate { numPatTests = numPatTests vstate + 1 }

--- Increments the number of test of possible failure calls.
incFailTestInStats :: VStateM ()
incFailTestInStats =
  modify $ \vstate -> vstate { numFailTests = numFailTests vstate + 1 }

--- Increments the number of preconditions. If the first argument is true,
--- a precondition has been verified.
addPreCondToStats :: String -> Bool -> VStateM ()
addPreCondToStats pc verified =
  if verified then modify $ \vst -> vst { vPreCond = pc : vPreCond vst }
              else modify $ \vst -> vst { uPreCond = pc : uPreCond vst }

--- Adds an operation to the already processed operations with postconditions.
--- If the second argument is true, the postcondition of this operation
--- has been verified.
addPostCondToStats :: String -> Bool -> VStateM ()
addPostCondToStats pc verified =
  if verified then modify $ \vst -> vst { vPostCond = pc : vPostCond vst }
              else modify $ \vst -> vst { uPostCond = pc : uPostCond vst }

--- Adds a new typed FlatCurry program to the state.
addProgsToState :: [TAProg] -> VStateM ()
addProgsToState progs =
  modify $ \vstate -> vstate { currTAProgs = currTAProgs vstate ++ progs }

--- Looks up a program from a module name
lookupProg :: ModuleName -> VStateM TAProg
lookupProg modname = do
  vst <- get
  case find (\p -> progName p == modname) (currTAProgs vst) of
    Nothing -> error $ "Missing program " ++ modname
    Just p -> return p

---------------------------------------------------------------------------
--- Selects the type declaration of a type constructor from the state.
tdeclOf :: QName -> VStateM (Maybe TypeDecl)
tdeclOf tcons@(mn,_) = do
  vst <- get
  return $ maybe Nothing
           (\p -> find (\td -> typeName td == tcons) (progTypes p))
           (find (\p -> progName p == mn) (currTAProgs vst))

---------------------------------------------------------------------------
