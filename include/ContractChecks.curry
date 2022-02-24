------------------------------------------------------------------------------
-- Auxiliary operations for contract checking.
-- If the contract tool adds some unverified contracts to a program,
-- the definition of these operations are also added.

--- Auxiliary operation to check the validity of a precondition for
--- some function call.
--- For this purpose, a function call
---
---     (f x1 ... xn)
---
--- is transformed into the new call
---
---     checkPreCond (f x1 ... xn) (f'pre x1 ... xn) "f" (x1,...,xn)
---
checkPreCond :: Show a => b -> Bool -> String -> a -> b
checkPreCond x pc fn args =
  if pc
    then x
    else error $ "Precondition of operation '" ++ fn ++
                 "' not satisfied for arguments:\n" ++ show args


--- Auxiliary operation to check the validity of a given postcondition.
--- For this purpose, each rule
---
---     f x1 ... xn = rhs
---
--- is transformed into the new rule
---
---     f x1 ... xn = checkPostCond rhs (f'post x1 ... xn) "f" (x1,...,xn)
---
checkPostCond :: (Show a, Show b) => b -> (b -> Bool) -> String -> a -> b
checkPostCond rhs fpost fname args =
  if fpost rhs
    then rhs
    else error $ "Postcondition of operation '" ++ fname ++
                 "' failed for arguments/result:\n" ++
                 show args ++ " -> " ++ show rhs

------------------------------------------------------------------------------
-- Since there are in general no `Show` instances for arbitrary operations
-- (e.g., polymorphic, higher-order), we provide type-specialized variants
-- of contract checking operations.

checkPreCond_Int :: b -> Bool -> String -> Int -> b
checkPreCond_Int r pc fn x = checkPreCond r pc fn x

-- If there is no type-specialization possible, we provide a variant
-- where the arguments are not shown.
checkPreCond_Any :: b -> Bool -> String -> a -> b
checkPreCond_Any x pc fn _ =
  if pc
    then x
    else error $ "Precondition of operation '" ++ fn ++
                 "' not satisfied for some arguments!"

checkPostCond_Int_Int :: Int -> (Int -> Bool) -> String -> Int -> Int
checkPostCond_Int_Int r pc fn x = checkPostCond r pc fn x

-- If there is no type-specialization possible, we provide a variant
-- where the arguments/result are not shown.
checkPostCond_Any_Any :: b -> (b -> Bool) -> String -> a -> b
checkPostCond_Any_Any rhs fpost fname _ =
  if fpost rhs
    then rhs
    else error $ "Postcondition of operation '" ++ fname ++
                 "' failed for some arguments/result!"

------------------------------------------------------------------------------
