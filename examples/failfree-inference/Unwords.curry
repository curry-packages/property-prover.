--- Accumulates a non-empty list from right to left:
-- foldr1'nonfail :: (a -> a -> a) -> [a] -> Bool
-- foldr1'nonfail _ xs = not (null xs)

--- Accumulates a non-empty list from right to left:
foldr1                :: (a -> a -> a) -> [a] -> a
foldr1 _ [x]          = x
foldr1 f (x:xs@(_:_)) = f x (foldr1 f xs)

unwords    :: [String] -> String
unwords ws = if null ws
               then []
               else foldr1 (\w s -> w ++ ' ':s) ws
