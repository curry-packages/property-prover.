------------------------------------------------------------------------------
-- Non-failure conditions for operations of module List.

transpose'nonfail :: [[a]] -> Bool
transpose'nonfail _ = False

last'nonfail :: [a] -> Bool
last'nonfail xs = not (null xs)

init'nonfail :: [a] -> Bool
init'nonfail xs = not (null xs)

maximum'nonfail :: Ord a => [a] -> Bool
maximum'nonfail xs = not (null xs)

maximumBy'nonfail :: (a -> a -> Ordering) -> [a] -> Bool
maximumBy'nonfail _ xs = not (null xs)

minimum'nonfail :: Ord a => [a] -> Bool
minimum'nonfail xs = not (null xs)

minimumBy'nonfail :: (a -> a -> Ordering) -> [a] -> Bool
minimumBy'nonfail _ xs = not (null xs)

cycle'nonfail :: [a] -> Bool
cycle'nonfail xs = not (null xs)

------------------------------------------------------------------------------

