-----------------------------------------------------------------------------
--- Some operations to read type-annotated FlatCurry programs.
---
--- @author  Michael Hanus
--- @version May 2021
---------------------------------------------------------------------------

module FlatCurry.Typed.Read where

import Control.Monad                 ( unless, when )
import Control.Monad.Trans.Class     ( lift )
import Control.Monad.Trans.State     ( gets )
import Data.List                     ( find, nub )
import Data.Maybe                    ( fromMaybe, fromJust )
import System.Directory              ( doesFileExist, removeFile )

-- Imports from dependencies:
import FlatCurry.TypeAnnotated.Files ( readTypeAnnotatedFlatCurry
                                     , readTypeAnnotatedFlatCurryFile
                                     , typeAnnotatedFlatCurryFileName )
import FlatCurry.Annotated.Goodies
import System.CurryPath              ( getLoadPathForModule, inCurrySubdir
                                     , lookupModuleSource )
import System.FilePath               ( (</>) )
import System.FrontendExec           ( FrontendTarget(TAFCY)
                                     , callFrontendWithParams, defaultParams
                                     , setQuiet )

import FlatCurry.Typed.Goodies
import FlatCurry.Typed.Names
import FlatCurry.Typed.Simplify
import FlatCurry.Typed.Types
import PackageConfig                 ( packagePath )
import ToolOptions
import VerifierState

----------------------------------------------------------------------------
--- Reads a typed FlatCurry program together with a possible `_SPEC` program
--- (containing further contracts) and simplify some expressions
--- (see module `FlatCurry.Typed.Simplify`).
readSimpTypedFlatCurryWithSpec :: String -> VStateM TAProg
readSimpTypedFlatCurryWithSpec mname =
  readTypedFlatCurryWithSpec mname >>= return . simpProg

--- Reads a typed FlatCurry program together with a possible `_SPEC` program
--- (containing further contracts).
--- All leading `ForallType` quantifiers are removed from function
--- signatures since they are not relevant here.
readTypedFlatCurryWithSpec :: String -> VStateM TAProg
readTypedFlatCurryWithSpec mname = do
  printWhenStatus $ "Loading typed FlatCurry program '" ++ mname ++ "'"
  prog <- lift $ readTypedFlatCurryWithoutForall mname
  mbspec   <- lift $ readTypedFlatCurryFromPath "include" specName
  case mbspec of
    Nothing -> return prog
    Just specprog -> do
      printWhenStatus $ "Adding '" ++ specName ++ "'"
      return $ unionTAProg prog $ rnmProg mname specprog
 where
  specName = mname ++ "_SPEC"

--- Reads a typed FlatCurry program from the load path or the given path.
--- All leading `ForallType` quantifiers are removed from function signatures.
readTypedFlatCurryFromPath :: String -> String -> IO (Maybe TAProg)
readTypedFlatCurryFromPath path mname = do
  loadpath <- getLoadPathForModule mname
  let path' = if null path then loadpath else (packagePath </> path) : loadpath
  mbsource <- lookupModuleSource path' mname
  case mbsource of
    Nothing              -> return Nothing
    Just (dir, filepath) -> do
      let afcyfile = inCurrySubdir dir </> (mname ++ ".afcy")
      unless (mname == "Prelude") $
        doesFileExist afcyfile >>= flip when (removeFile afcyfile)
      callFrontendWithParams TAFCY (setQuiet True defaultParams) filepath
      readTypeAnnotatedFlatCurryFile
        (dir </> typeAnnotatedFlatCurryFileName mname)
          >>= return . Just . updProgFuncs (map (updFuncType stripForall))

--- Reads a typed FlatCurry program and remove all leading
--- `ForallType` quantifiers from function signatures.
readTypedFlatCurryWithoutForall :: String -> IO TAProg
readTypedFlatCurryWithoutForall mname =
  readTypedFlatCurryFromPath "" mname
    >>= return . fromMaybe
      (error $ "Typed FlatCurry program '" ++ mname ++ "' could not be found")

-- Strip outermost `ForallType` quantifications.
stripForall :: TypeExpr -> TypeExpr
stripForall texp = case texp of
  ForallType _ te  -> stripForall te
  _                -> texp

----------------------------------------------------------------------------
--- Extract all user-defined typed FlatCurry functions that might be called
--- by a given list of functions.
getAllFunctions :: [TAFuncDecl] -> [QName] -> VStateM [TAFuncDecl]
getAllFunctions currfuncs newfuns = do
  currmods <- gets currTAProgs
  getAllFuncs currmods newfuns
 where
  getAllFuncs _ [] = return $ reverse currfuncs
  getAllFuncs currmods (newfun : newfuncs)
    | newfun `elem` map (pre . fst) transPrimCons ++ map funcName currfuncs
      || isPrimOp newfun
    = getAllFunctions currfuncs newfuncs
    | fst newfun `elem` map progName currmods
    = maybe
        -- if we don't find the qname, it must be a constructor:
        (getAllFunctions currfuncs newfuncs)
        (\fdecl -> getAllFunctions
                      (fdecl : currfuncs)
                      (newfuncs ++ nub (funcsOfFuncDecl fdecl)))
        (find (\fd -> funcName fd == newfun)
              (progFuncs
                 (fromJust (find (\m -> progName m == fst newfun) currmods))))
    | otherwise -- we must load a new module
    = do let mname = fst newfun
         printWhenStatus $
           "Loading module '" ++ mname ++ "' for '"++ snd newfun ++"'"
         newmod <- lift $ readTypedFlatCurryWithoutForall mname
          >>= return . simpProg
         addProgsToState [newmod]
         getAllFunctions currfuncs (newfun : newfuncs)

----------------------------------------------------------------------------
