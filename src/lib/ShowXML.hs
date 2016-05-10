{-# LANGUAGE FlexibleInstances #-}

module ShowXML where

import qualified Data.Text      as T
import           Data.XML.Types

class ShowXML t where
  showXML :: t -> String

instance ShowXML Name where
  showXML (Name ln Nothing   _) = T.unpack ln
  showXML (Name ln (Just ns) _) = T.unpack ns ++ ":" ++ T.unpack ln

instance ShowXML Content where
  showXML (ContentText t) = T.unpack t
  showXML (ContentEntity t) = T.unpack t

instance ShowXML [Content] where
  showXML [] = ""
  showXML [e] = showXML e
  showXML (h:t) = showXML h ++ " " ++ showXML t

instance ShowXML Event where
  showXML (EventBeginElement n a) =
    "<" ++ name ++ attrs ++ ">"
    where
      name = showXML n
      attrs = concatMap
              (\ (n', a') -> " " ++ showXML n' ++ "=\"" ++ showXML a' ++ "\"")
              a
  showXML e = show e

instance ShowXML a => ShowXML (Maybe a) where
  showXML Nothing = "Nothing"
  showXML (Just a) = showXML a
