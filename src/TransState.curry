module TransState where

import Control.Monad.Trans.State   ( StateT, get, put )
import Data.List                   ( elemIndex, find )
import Data.Maybe                  ( fromJust )

import Language.SMTLIB.Goodies
import qualified Language.SMTLIB.Types as SMT

import FlatCurry.Typed.Types
import VerifierState

---------------------------------------------------------------------------
-- The state of the transformation process contains
-- * the current assertion
-- * a fresh variable index
-- * a list of all introduced variables and their types:
data TransState = TransState
  { cAssertion :: SMT.Term
  , freshVar   :: Int
  , varTypes   :: [(Int, TypeExpr, Maybe (QName, Int, Int))]
  }

makeTransState :: Int -> [(Int, TypeExpr, Maybe (QName, Int, Int))]
               -> TransState
makeTransState = TransState true

emptyTransState :: TransState
emptyTransState = makeTransState 0 []

-- The type of the state monad contains the transformation state.
--type TransStateM a = State TransState a
type TransStateM a = StateT TransState (StateT VState IO) a

-- Gets the current fresh variable index of the state.
getFreshVarIndex :: TransStateM Int
getFreshVarIndex = get >>= return . freshVar

-- Sets the fresh variable index in the state.
setFreshVarIndex :: Int -> TransStateM ()
setFreshVarIndex fvi = do
  st <- get
  put $ st { freshVar = fvi }

-- Gets a fresh variable index and increment the index in the state.
getFreshVar :: TransStateM Int
getFreshVar = do
  st <- get
  put $ st { freshVar = freshVar st + 1 }
  return $ freshVar st

-- Increments fresh variable index.
incFreshVarIndex :: TransState -> TransState
incFreshVarIndex st = st { freshVar = freshVar st + 1 }

-- Gets the variables and their types stored in the state.
getVarTypes :: TransStateM [(Int, TypeExpr, Maybe (QName, Int, Int))]
getVarTypes = get >>= return . varTypes

-- Adds variables and their types to the state.
addVarTypes :: [(Int,TypeExpr)] -> TransStateM ()
addVarTypes vts = do
  st <- get
  put $ st { varTypes = (map (\(x,y) -> (x, y, Nothing)) vts) ++ varTypes st }

-- Sets the function name associated with a variable to the given name for the
-- variables with the given indices.
setNameOfVars :: QName -> [Int] -> TransStateM ()
setNameOfVars name is = do
  st <- get
  let funcindex = maybe 1 ((+1) . third . fromJust)
                  $ find (maybe False ((== name) . fst3))
                  $ map third $ varTypes st
      vartypes' =
        map (\(i,t,s) -> if i `elem` is
              then (i, t,
                     Just (name, 1 + (fromJust $ elemIndex i is), funcindex))
              else (i,t,s))
            (varTypes st)
  put $ st { varTypes = vartypes' }
 where
  fst3  (x,_,_) = x
  third (_,_,x) = x

-- Gets the current assertion stored in the state.
getAssertion :: TransStateM SMT.Term
getAssertion = get >>= return . cAssertion

-- Sets the current assertion in the state.
setAssertion :: SMT.Term -> TransStateM ()
setAssertion formula = do
  st <- get
  put $ st { cAssertion = formula }

-- Add a formula to the current assertion in the state by conjunction.
addToAssertion :: SMT.Term -> TransStateM ()
addToAssertion formula = do
  st <- get
  put $ st { cAssertion = tand [cAssertion st, formula] }
