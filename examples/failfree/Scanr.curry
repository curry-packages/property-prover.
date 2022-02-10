--- Example for using post-conditions for verification:
--- The successful verification requires option `--contract`!

--- `scanr` is the right-to-left dual of `scanl`.
scanr             :: (a -> b -> b) -> b -> [a] -> [b]
scanr _ q0 []     =  [q0]
scanr f q0 (x:xs) =  f x (head (scanr f q0 xs)) : scanr f q0 xs
                     --where qs@(q:_) = scanr f q0 xs

scanr'post :: (a -> b -> b) -> b -> [a] -> [b] -> Bool
scanr'post f y xs ys = not (null ys)

--- `scanr1` is a variant of `scanr` that has no starting value argument.
scanr1                :: (a -> a -> a) -> [a] -> [a]
scanr1 _ []           =  []
scanr1 _ [x]          =  [x]
scanr1 f (x:xs@(_:_)) =  f x (head (scanr1 f xs)) : (scanr1 f xs)
                        -- where qs@(q:_) = scanr1 f xs

scanr1'post :: (a -> a -> a) -> [a] -> [a] -> Bool
scanr1'post f xs ys = not (null ys)
