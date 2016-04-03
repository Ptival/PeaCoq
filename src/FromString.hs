{-# LANGUAGE FlexibleInstances #-}

module FromString where

{-
'FromString' is a little like 'Read', but does not need be inverse of 'Show'.
In particular, 'String' is read as-is.
-}
class FromString a where
  fromString :: String -> a

instance FromString String where
  fromString = id

instance FromString Int where
  fromString = read
