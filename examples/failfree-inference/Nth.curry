nth :: [a] -> Int -> a
nth (x:xs) n | n==0 = x
             | n>0  = nth xs (n-1)

-- nth'nonfail :: [a] -> Int -> Bool
-- nth'nonfail xs n = n >= 0 && length (take (n+1) xs) == n+1

-- from the Prelude:

--- Computes the length of a list.
length          :: [_] -> Int
length []       = 0
length (_:xs)   = 1 + length xs

--- Returns prefix of length n.
take              :: Int -> [a] -> [a]
take n l          = if n<=0 then [] else takep n l
 where
  takep _ []     = []
  takep m (x:xs) = x : take (m-1) xs
