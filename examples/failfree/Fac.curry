faci :: Int -> Int
faci n = if n == 0 then 1 else n * faci (n - 1)

facg'nonfail :: Int -> Bool
facg'nonfail n = n >= 0

facg'pre :: Int -> Bool
facg'pre n = n >= 0

facg'post :: Int -> Int -> Bool
facg'post n f = f > 0

facg :: Int -> Int
facg n | n == 0 = 1
       | n >  0 = n * facg (n - 1)
