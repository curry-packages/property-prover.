-- This is an example containing operations from the standard library Char.
-- The verification of this example requires reasoning on the characters,
-- the operation Prelude.ord and the axiomatization of the operation isLower
-- as an SMT formula.

--- Returns true if the argument is an lowercase letter.
isLower         :: Char -> Bool
isLower c       =  c >= 'a' && c <= 'z'

--- Converts lowercase into uppercase letters.
toUpper         :: Char -> Char
toUpper c       |  isLower c = chr (ord c - ord 'a' + ord 'A')
                |  otherwise = c

