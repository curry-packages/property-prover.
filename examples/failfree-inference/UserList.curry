--- Test for verification with user-defined polymorphic lists.

data MyList a = Nil | Cons a (MyList a)

isNull :: MyList a -> Bool
isNull Nil        = True
isNull (Cons _ _) = False

--- Defining head on these lists:
head :: MyList a -> a
head (Cons x _) = x

-- head'nonfail :: MyList a -> Bool
-- head'nonfail xs = not (isNull xs)

main :: Int
main = head (Cons 1 Nil)
