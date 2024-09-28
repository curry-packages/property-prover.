------------------------------------------------------------------------------
-- Non-failure conditions for Prelude operations.

solve'nonfail :: Bool -> Bool
solve'nonfail x = x

doSolve'nonfail :: Bool -> Bool
doSolve'nonfail x = x

head'nonfail :: [a] -> Bool
head'nonfail xs = not (null xs)

tail'nonfail :: [a] -> Bool
tail'nonfail xs = not (null xs)

foldr1'nonfail :: (a -> a -> a) -> [a] -> Bool
foldr1'nonfail _ xs = not (null xs)

foldl1'nonfail :: (a -> a -> a) -> [a] -> Bool
foldl1'nonfail _ xs = not (null xs)

anyOf'nonfail :: [a] -> Bool
anyOf'nonfail xs = not (null xs)

-- Non-failure condition for `&>`.
op_x263E'nonfail :: Bool -> a -> Bool
op_x263E'nonfail x _ = x

-- Non-failure condition for `!!`.
op_x2121'nonfail :: [a] -> Int -> Bool
op_x2121'nonfail xs n = n >= 0 && length (take (n+1) xs) == n+1

showTuple'nonfail :: [ShowS] -> String -> Bool
showTuple'nonfail xs _ = not (null xs)

-- Non-failure condition for '_impl#divMod#Prelude.Integral#Prelude.Int#',
-- i.e., operation `divMod` in instance `Integral Int`.
op_x5F696D706C236469764D6F64235072656C7564652E496E74656772616C235072656C7564652E496E7423'nonfail :: Int -> Int -> Bool
op_x5F696D706C236469764D6F64235072656C7564652E496E74656772616C235072656C7564652E496E7423'nonfail x y = y /= 0

-- Non-failure condition for '_impl#quotRem#Prelude.Integral#Prelude.Int#',
-- i.e., operation `quotRem` in instance `Integral Int`.
op_x5F696D706C2371756F7452656D235072656C7564652E496E74656772616C235072656C7564652E496E7423'nonfail :: Int -> Int -> Bool
op_x5F696D706C2371756F7452656D235072656C7564652E496E74656772616C235072656C7564652E496E7423'nonfail x y = y /= 0

------------------------------------------------------------------------------
-- External operations:

-- Non-failure condition for `=:=`.
failed'nonfail :: Bool
failed'nonfail = False

-- Non-failure condition for `=:=`.
op_x3D3A3D'nonfail :: a -> a -> Bool
op_x3D3A3D'nonfail _ _ = False

-- Non-failure condition for `=:<=`.
op_x3D3A3C3D'nonfail :: a -> a -> Bool
op_x3D3A3C3D'nonfail _ _ = False

-- Non-failure condition for `=:<<=`.
op_x3D3A3C3C3D'nonfail :: a -> a -> Bool
op_x3D3A3C3C3D'nonfail _ _ = False

-- Non-failure condition for `&`.
op_x26'nonfail :: Bool -> Bool -> Bool
op_x26'nonfail x y = x && y

div_'nonfail :: Int -> Int -> Bool
div_'nonfail x y = y /= 0

mod_'nonfail :: Int -> Int -> Bool
mod_'nonfail x y = y /= 0

divMod_'nonfail :: Int -> Int -> Bool
divMod_'nonfail x y = y /= 0

quot_'nonfail :: Int -> Int -> Bool
quot_'nonfail x y = y /= 0

rem_'nonfail :: Int -> Int -> Bool
rem_'nonfail x y = y /= 0

quotRem_'nonfail :: Int -> Int -> Bool
quotRem_'nonfail x y = y /= 0

------------------------------------------------------------------------------

