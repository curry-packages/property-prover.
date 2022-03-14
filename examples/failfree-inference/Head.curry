--- Computes the first element of a list.
-- head'nonfail :: [a] -> Bool
-- head'nonfail xs = not (null xs)

head :: [a] -> a
head (x:_)      = x

main :: Char
main = head "12"
