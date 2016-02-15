{-# LANGUAGE FlexibleInstances #-}

module ToXML where

import Text.HTML.TagSoup.Entity (escapeXML)

class ToXML a where
  xml :: a -> String

instance ToXML () where
  xml () = "<unit/>"

instance ToXML Bool where
  xml True  = "<bool val=\"true\"/>"
  xml False = "<bool val=\"false\"/>"

instance {-# OVERLAPS #-} ToXML String where
  xml s = "<string>" ++ escapeXML s ++ "</string>"

instance ToXML Int where
  xml i = "<int>" ++ show i ++ "</int>"

instance {-# OVERLAPPABLE #-} ToXML a => ToXML [a] where
  xml [] = "<list/>"
  xml l  = unlines ("<list>" : map xml l ++ ["</list>"])

instance ToXML a => ToXML (Maybe a) where
  xml Nothing  = "<option val=\"none\"/>"
  xml (Just x) = "<option val=\"some\">" ++ xml x ++ "</option>"

instance (ToXML a, ToXML b) => ToXML (a, b) where
  xml (l, r) =
    "<pair>\n"
    ++ unlines [xml l, xml r]
    ++ "</pair>"

mkTag :: ToXML a => String -> String -> a -> String
mkTag name val contents =
  "<" ++ name ++ " val=\"" ++ val ++ "\">\n"
  ++ xml contents
  ++ "\n</" ++ name ++ ">"
