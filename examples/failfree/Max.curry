maximum'nonfail :: Ord a => [a] -> Bool
maximum'nonfail xs = not (null xs)

maximum :: Ord a => [a] -> a
maximum xs@(_:_) =  foldl1 max xs
