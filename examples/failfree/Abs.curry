-- To detect the non-failure of the following operation,
-- reasoning over integers is required:
abs :: Int -> Int
abs x | x>=0 = x
      | x<0  = 0 - x

-- It must be proved that the guards are complete since the definition
-- above is translated into the following definition:
absif :: Int -> Int
absif x = if x>=0 then x
                  else if x<0 then (0 - x)
                              else failed
