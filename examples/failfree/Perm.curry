-- Non-deterministic list insertion.
-- Both rules are overlapping. Thus, if the Curry evaluator
-- decides to take the second rule, the evaluation fails on the
-- empty list.
ins :: a -> [a] -> [a]
ins x ys     = x : ys
ins x (y:ys) = y : ins x ys
-- Therefore, the following non-fail condition is required:
ins'nonfail :: a -> [a] -> Bool
ins'nonfail _ _ = False

-- To provide a non-failing version of list insertion, we define
-- a non-deterministic list insertion by pattern matching:
insP :: a -> [a] -> [a]
insP x []     = [x]
insP x (y:ys) = x : y : ys  ?  y : insP x ys

-- Exploiting non-deterministic list insertion, one can easily define
-- list permutations:
perm :: [a] -> [a]
perm []     = []
perm (x:xs) = insP x (perm xs)
