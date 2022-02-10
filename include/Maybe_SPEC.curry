------------------------------------------------------------------------------
-- Non-failure conditions for operations of module Maybe.

import Maybe ( isJust )

fromJust'nonfail :: Maybe a -> Bool
fromJust'nonfail x = isJust x

------------------------------------------------------------------------------

