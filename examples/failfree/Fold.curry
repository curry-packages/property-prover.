--- Accumulates a non-empty list from right to left:
foldr1'nonfail :: (a -> a -> a) -> [a] -> Bool
foldr1'nonfail _ xs = not (null xs)

--- Accumulates a non-empty list from right to left:
foldr1                :: (a -> a -> a) -> [a] -> a
foldr1 _ [x]          = x
foldr1 f (x:xs@(_:_)) = f x (foldr1 f xs)

--- Accumulates all list elements by applying a binary operator from
--- left to right.
foldl            :: (a -> b -> a) -> a -> [b] -> a
foldl _ z []     = z
foldl f z (x:xs) = foldl f (f z x) xs

--- Accumulates a non-empty list from left to right.
foldl1'nonfail :: (a -> a -> a) -> [a] -> Bool
foldl1'nonfail _ xs = not (null xs)

foldl1           :: (a -> a -> a) -> [a] -> a
foldl1 f (x:xs)  = foldl f x xs
