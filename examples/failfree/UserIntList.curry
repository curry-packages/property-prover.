--- Test for verification with user-defined lists.

data MyList = Nil | Cons Int MyList

isNull :: MyList -> Bool
isNull Nil        = True
isNull (Cons _ _) = False

--- Defining head on these lists:
head :: MyList -> Int
head (Cons x _) = x

head'nonfail :: MyList -> Bool
head'nonfail xs = not (isNull xs)

main :: Int
main = head (Cons 1 Nil)
