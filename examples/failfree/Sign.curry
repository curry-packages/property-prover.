-- To detect the non-failure of the following operation,
-- reasoning over integers is required:
sig :: Int -> Int
sig x | x>0  = 1
      | x==0 = 0
      | x<0  = -1

-- It must be proved that the guards are complete since the definition
-- above is translated into the following definition:
sigif :: Int -> Int
sigif x = if x>0
            then 1
            else if x==0 then 0
                         else if x<0 then -1
                                     else failed
