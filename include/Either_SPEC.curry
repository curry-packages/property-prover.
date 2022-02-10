import Either ( isLeft, isRight )

fromLeft'nonfail :: Either a b -> Bool
fromLeft'nonfail x = isLeft x

fromRight'nonfail :: Either a b -> Bool
fromRight'nonfail x = isRight x
