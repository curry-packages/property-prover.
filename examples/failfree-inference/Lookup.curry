--- Testing handling of generic equalities.
--- The tool translates these into builtin equality, i.e.,
--- it assumes that each equality instance really defines
--- an equality relation.

--- Looks up a key in an association list.
lookup :: Eq a => a -> [(a, b)] -> Maybe b
lookup _ []          = Nothing
lookup k ((x,y):xys) | k==x      = Just y
                     | otherwise = lookup k xys

