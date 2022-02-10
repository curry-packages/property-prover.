--- An example for verification with user-defined data types.

--- Natural numbers defined in Peano representation.
data Nat = Z | S Nat
  deriving Eq

--- Transforms a natural number into a standard integer.
fromNat :: Nat -> Int
fromNat Z     = 0
fromNat (S n) = 1 + fromNat n

--- Addition on natural numbers.
add :: Nat -> Nat -> Nat
add Z     n = n
add (S m) n = S(add m n)

--- The predecessor operation is partially defined.
pred :: Nat -> Nat
pred (S m) = m

pred'nonfail :: Nat -> Bool
pred'nonfail x = not (x==Z)

main :: Nat
main = pred (S Z)
