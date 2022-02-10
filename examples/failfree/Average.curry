--- Verification of average operation
--- The verification requires option `--contract`!

-- This simple definition contains a possible failure:
--
--      average xs = sum xs `div` length xs
--
-- This non-failing definition requires the postcondition of length, i.e.,
-- it can be verified as fail-free with option --contract|-c
average :: [Int] -> Int
average xs = if null xs then 0
                        else sum xs `div` length xs

-- From library `List`:
sum :: [Int] -> Int
sum = foldr (+) 0

-- From the prelude but with a postcondition:
length :: [a] -> Int
length []     = 0
length (_:xs) = 1 + length xs

length'post :: [a] -> Int -> Bool
length'post xs n = (null xs && n==0) || (not (null xs) && n>0)

