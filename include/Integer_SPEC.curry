------------------------------------------------------------------------------
-- Non-failure conditions for operations of module Integer.

-- Non-failure condition for `^`.
op_x5E'nonfail :: Int -> Int -> Bool
op_x5E'nonfail _ b = b >= 0

pow'nonfail :: Int -> Int -> Bool
pow'nonfail _ b = b >= 0

ilog'nonfail :: Int -> Bool
ilog'nonfail n = n > 0

isqrt'nonfail :: Int -> Bool
isqrt'nonfail n = n >= 0

factorial'nonfail :: Int -> Bool
factorial'nonfail n = n >= 0

factorial'post :: Int -> Int -> Bool
factorial'post _ f = f > 0

binomial'nonfail :: Int -> Int -> Bool
binomial'nonfail n m = m>0 && n>=m

maxlist'nonfail :: Ord a => [a] -> Bool
maxlist'nonfail xs = not (null xs)

minlist'nonfail :: Ord a => [a] -> Bool
minlist'nonfail xs = not (null xs)

bitTrunc'nonfail :: Int -> Int -> Bool
bitTrunc'nonfail n _ = n >= 0

------------------------------------------------------------------------------

