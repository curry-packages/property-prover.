-------------------------------------------------------------------------
--- The options of the contract verification tool together with some
--- related operations.
---
--- @author Michael Hanus
--- @version May 2021
-------------------------------------------------------------------------

module ToolOptions
  ( Options(..), defaultOptions, processOptions
  )
 where

import Control.Monad         ( when, unless )
import Data.Char             ( toUpper )
import System.Console.GetOpt
import Numeric               ( readNat )
import System.Process        ( exitWith )

import System.CurryPath      ( stripCurrySuffix )

data Options = Options
  { optVerb     :: Int    -- verbosity (0: quiet, 1: status, 2: interm, 3: all)
  , optHelp     :: Bool   -- if help info should be printed
  , optName     :: String -- show only the name of a nonfail condition
  , optError    :: Bool   -- should `error` be considered as a failing function?
  , optRec      :: Bool   -- recursive, i.e., verify imported modules first?
  , optConFail  :: Bool   -- consider pre/postconditions for failfree
                          -- verification?
  , optStrict   :: Bool   -- verify precondition w.r.t. strict evaluation?
                          -- in this case, we assume that all operations are
                          -- strictly evaluated which might give better results
                          -- but not not be correct if some argument is not
                          -- demanded (TODO: add demand analysis to make it
                          -- safe and powerful)
  , optWrite    :: Bool   -- if the modified flat curry program should be
                          -- written back
  , optFailfree :: Bool   -- verify non-failing functions?
  , optContract :: Int    -- contract behavior (0: nothing, 1: add, 2: verify)
  , optTime     :: Bool   -- show elapsed verification time?
  , optExamples :: Int    -- the maximum number of counter examples that should
                          -- be generated
  }

defaultOptions :: Options
defaultOptions = Options 1 False "" False False False False True True 2 False 3

--- Process the actual command line argument and return the options
--- and the name of the main program.
processOptions :: String -> [String] -> IO (Options,[String])
processOptions banner argv = do
  let (funopts, args, opterrors) = getOpt Permute options argv
      opts = foldl (flip id) defaultOptions funopts
  unless (null opterrors)
         (putStr (unlines opterrors) >> printUsage >> exitWith 1)
  when (optHelp opts) (printUsage >> exitWith 0)
  return (opts, map stripCurrySuffix args)
 where
  printUsage = putStrLn (banner ++ "\n" ++ usageText)

-- Help text
usageText :: String
usageText =
  usageInfo ("Usage: curry-failfree [options] <module names>\n") options

-- Definition of actual command line options.
options :: [OptDescr (Options -> Options)]
options =
  [ Option "h?" ["help"]
           (NoArg (\opts -> opts { optHelp = True }))
           "print help and exit"
  , Option "n" ["name"]
            (ReqArg (\s opts -> opts { optName = s }) "<f>") $
            "show only the name of a non-fail condition\n" ++
            "and pre- and postconditions"
  , Option "m" ["checkmode"] (ReqArg readContractMode "n|a|v") $ unlines
             [ "behavior of contract checking:"
             , "a: only add contract checks"
             , "v: verify contracts (default)"
             , "n: do nothing"
             ]
  , Option "f" ["no-failfree"]
           (NoArg (\opts -> opts { optFailfree = False }))
           "don't verify non-fail conditions"
  , Option "q" ["quiet"]
           (NoArg (\opts -> opts { optVerb = 0 }))
           "run quietly (no output, only exit code)"
  , Option "v" ["verbosity"]
            (OptArg (maybe (checkVerb 2) (safeReadNat checkVerb)) "<n>")
            $ unlines
              [ "verbosity level:"
              , "0: quiet (same as `-q')"
              , "1: show status messages (default)"
              , "2: show intermediate results (same as `-v')"
              , "3: show all details (e.g., SMT scripts)"
              ]
  , Option "e" ["error"]
           (NoArg (\opts -> opts { optError = True }))
           "consider 'Prelude.error' as a failing operation"
  , Option "r" ["recursive"]
           (NoArg (\opts -> opts { optRec = True }))
           "recursive, i.e., verify imported modules first"
  , Option "c" ["contract"]
            (NoArg (\opts -> opts { optConFail = True }))
           "consider contracts (pre/postcondition)\nfor failfree verification"
  , Option "s" ["strict"]
           (NoArg (\opts -> opts { optStrict = True }))
           "check contracts w.r.t. strict evaluation\nstrategy"
  , Option "w" ["no-write"]
           (NoArg (\opts -> opts { optWrite = False }))
           "do not overwrite the FlatCurry program\nwith the modified version"
  , Option "t" ["time"]
           (NoArg (\opts -> opts { optTime = True }))
           "show total verification time for each module"
  , Option "x" ["examples"]
           (ReqArg (safeReadNat (\n opts -> opts {optExamples = n})) "<n>")
           "maximum number of counter examples to generate"
  ]
 where
  safeReadNat opttrans s opts = case readNat s of
    [(n,"")] -> opttrans n opts
    _        -> error "Illegal number argument (try `-h' for help)"

  checkVerb n opts = if n>=0 && n<4
                       then opts { optVerb = n }
                       else error "Illegal verbosity level (try `-h' for help)"
  readContractMode s opts = case s of
    "n" -> opts { optContract = 0 }
    "a" -> opts { optContract = 1 }
    "v" -> opts { optContract = 2 }
    _   -> error "Illegal contract mode (try `-h' for help)"

-------------------------------------------------------------------------
