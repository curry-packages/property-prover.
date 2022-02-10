--- Example for using post-conditions for verification:
--- The successful verification requires option `--contract`!

-- non-failure could be verified with contracts, i.e., with option '-c':
split :: (a -> Bool) -> [a] -> [[a]]
split _ []     = [[]]
split p (x:xs) | p x       = [] : split p xs
               | otherwise = --let (ys:yss) = split p xs in (x:ys):yss
                             -- TODO: improve let reasoning in tool...
                             (x : head (split p xs)) : tail (split p xs)

split'post :: (a -> Bool) -> [a] -> [[a]] -> Bool
split'post p xs ys = not (null ys)
