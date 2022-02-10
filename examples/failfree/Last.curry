--- Returns the last element of a non-empty list.
last'nonfail :: [a] -> Bool
last'nonfail xs = not (null xs)

last :: [a] -> a
last [x]            = x
last (_ : xs@(_:_)) = last xs

--- Returns the input list with the last element removed.
init'nonfail :: [a] -> Bool
init'nonfail xs = not (null xs)

init :: [a] -> [a]
init [_]          = []
init (x:xs@(_:_)) = x : init xs

--- Is a list empty?
null :: [_] -> Bool
null []    = True
null (_:_) = False

lastOr :: [a] -> a -> a
lastOr xs x = if null xs then x
                         else last xs
