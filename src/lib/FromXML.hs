{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module FromXML where

import           Data.Conduit           (Consumer)
import           Data.Proxy
import qualified Data.Text              as T
import           Data.XML.Types         (Event)
import           Text.XML.Stream.Parse

import           Utils

{- Parsing from XML -}

type Parser a = Consumer Event IO a

class FromXML a where
  instanceName :: Proxy a -> String
  parseXML :: Parser (Maybe a)
  forceXML :: Parser a
  forceXML = force ("forceXML failed, at instance: " ++ instanceName (Proxy :: Proxy a)) parseXML

instance (FromXML a, FromXML b) => FromXML (Either a b) where
  instanceName Proxy = "Either"
  parseXML = tagName "union" (requireAttr "val") $ \ val ->
    case val of
    "in_l" -> Left  <$> forceXML
    "in_r" -> Right <$> forceXML
    _ -> error "union was neither in_l nor in_r"

instance {-# OVERLAPS #-} FromXML String where
  instanceName Proxy = "String"
  parseXML = tagNoAttr "string" (T.unpack <$> content)

instance FromXML a => FromXML [a] where
  instanceName Proxy = "List"
  parseXML = tagNoAttr "list" $ many parseXML

instance FromXML a => FromXML (Maybe a) where
  instanceName Proxy = "Maybe"
  parseXML = tagName "option" (requireAttr "val") $ \ val ->
    case val of
    "some" -> Just <$> forceXML
    "none" -> return Nothing
    _ -> error "option string was neither some nor none"
  forceXML = force "Maybe" parseXML

instance FromXML Int where
  instanceName Proxy = "Int"
  parseXML = tagNoAttr "int" castContent

instance (FromXML a, FromXML b) => FromXML (a, b) where
  instanceName Proxy = "Pair"
  parseXML = tagNoAttr "pair" $ do
    a <- forceXML
    b <- forceXML
    return (a, b)

instance FromXML () where
  instanceName Proxy = "()"
  parseXML = tagNoAttr "unit" (return ())

instance FromXML Bool where
  instanceName Proxy = "Bool"
  parseXML = tagName "bool" (requireAttr "val") $ \ val ->
    case val of
    "true"  -> return True
    "false" -> return False
    _ -> error "bool was neither true nor false"
