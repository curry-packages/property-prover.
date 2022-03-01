module Utils where

import           Data.List
  ( (\\), elemIndex, find, intersperse, maximum, minimum, partition, union )
import           FlatCurry.Typed.Goodies
import           FlatCurry.Typed.Types
import           Numeric                 ( readHex )

--- Tests whether the given branches of a case expressions
--- are a Boolean case distinction.
--- If yes, the expressions of the `False` and `True` branch
--- are returned.
testBoolCase :: [TABranchExpr] -> Maybe (TAExpr, TAExpr)
testBoolCase brs
  = if length brs /= 2 then Nothing else case (head brs, brs !! 1) of
    (ABranch (APattern _ (c1, _) _) e1, ABranch (APattern _ (c2, _) _) e2) ->
      if c1 == pre "False" && c2 == pre "True"
        then Just (e1, e2)
        else if c1 == pre "True" && c2 == pre "False"
          then Just (e2, e1)
          else Nothing
    _ -> Nothing

--- Shows a text with line numbers prefixed:
showWithLineNums :: String -> String
showWithLineNums txt
  = let txtlines  = lines txt
        maxlog    = ilog (length txtlines + 1)
        showNum n = replicate (maxlog - ilog n) ' ' ++ show n ++ ": "
    in unlines . zipWith (++) (map showNum [1 ..]) $ txtlines

--- The value of `ilog n` is the floor of the logarithm
--- in the base 10 of `n`.
--- Fails if `n &lt;= 0`.
--- For positive integers, the returned value is
--- 1 less the number of digits in the decimal representation of `n`.
---
--- @param n - The argument.
--- @return the floor of the logarithm in the base 10 of `n`.
ilog :: Int -> Int
ilog n | n > 0 = if n < 10 then 0 else 1 + ilog (n `div` 10)

-- Gets all type constructors of a type expression.
tconsOfTypeExpr :: TypeExpr -> [QName]
tconsOfTypeExpr (TVar _)            = []
tconsOfTypeExpr (FuncType a b)
  = tconsOfTypeExpr a `union` tconsOfTypeExpr b
tconsOfTypeExpr (TCons qName texps) = foldr (union . tconsOfTypeExpr) [qName]
  texps
tconsOfTypeExpr (ForallType _ te)   = tconsOfTypeExpr te

--- Encode special characters in strings  
encodeSpecialChars :: String -> String
encodeSpecialChars = concatMap encChar
 where
  encChar c | c `elem` "#$%[]()!,"
              = let oc = ord c
                in ['%', int2hex (oc `div` 16), int2hex (oc `mod` 16)]
            | otherwise = [c]

  int2hex i = if i < 10 then chr (ord '0' + i) else chr (ord 'A' + i - 10)

--- Translates urlencoded string into equivalent ASCII string.
decodeSpecialChars :: String -> String
decodeSpecialChars []       = []
decodeSpecialChars (c : cs)
  | c == '%' = let n = case readHex (take 2 cs) of
                     [(h, "")] -> h
                     _         -> 0
               in chr n : decodeSpecialChars (drop 2 cs)
  | otherwise = c : decodeSpecialChars cs