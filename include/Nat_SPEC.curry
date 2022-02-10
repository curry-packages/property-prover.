------------------------------------------------------------------------------
-- Non-failure conditions for operations of module Nat.

toNat'nonfail :: Int -> Bool
toNat'nonfail n = n >= 0

sub'nonfail :: Nat -> Nat -> Bool
sub'nonfail _ _ = False

------------------------------------------------------------------------------

