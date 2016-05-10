{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module ParseXML where

import           Control.Monad.Catch
import           Data.Conduit
import qualified Data.Text             as T
import           Data.XML.Types
import           Text.XML.Stream.Parse

{- Unpacking and casting -}

readUnpack :: Read a => T.Text -> a
readUnpack = read . T.unpack

unpackRequireAttr :: Name -> AttrParser String
unpackRequireAttr s = T.unpack <$> requireAttr s

castRequireAttr :: Read a => Name -> AttrParser a
castRequireAttr s = readUnpack <$> requireAttr s

unpackAttr :: Name -> AttrParser (Maybe String)
unpackAttr s = (T.unpack <$>) <$> attr s

castAttr :: Read a => Name -> AttrParser (Maybe a)
castAttr s = (readUnpack <$>) <$> attr s

unpackContent :: MonadThrow m => Consumer Event m String
unpackContent = T.unpack <$> content

castContent :: MonadThrow m => Read a => Consumer Event m a
castContent = readUnpack <$> content

{- Parsing from XML -}

type Parser a = Consumer Event IO a

class ParseXML a where
  parseXML :: Parser (Maybe a)
  forceXML :: Parser a
  forceXML = force "forceXML" parseXML

instance (ParseXML a, ParseXML b) => ParseXML (Either a b) where
  parseXML = tagName "union" (requireAttr "val") $ \ val ->
    case val of
    "in_l" -> Left  <$> forceXML
    "in_r" -> Right <$> forceXML
    _ -> error "union was neither in_l nor in_r"

instance {-# OVERLAPS #-} ParseXML String where
  parseXML = tagNoAttr "string" (T.unpack <$> content)

instance ParseXML a => ParseXML [a] where
  parseXML = tagNoAttr "list" $ many parseXML

instance ParseXML a => ParseXML (Maybe a) where
  parseXML = tagName "option" (requireAttr "val") $ \ val ->
    case val of
    "some" -> parseXML
    "none" -> return Nothing
    _ -> error "option string was neither some nor none"

instance ParseXML Int where
  parseXML = tagNoAttr "int" castContent

instance (ParseXML a, ParseXML b) => ParseXML (a, b) where
  parseXML = tagNoAttr "pair" $ do
    a <- forceXML
    b <- forceXML
    return (a, b)

instance ParseXML () where
  parseXML = tagNoAttr "unit" (return ())

instance ParseXML Bool where
  parseXML = tagName "bool" (requireAttr "val") $ \ val ->
    case val of
    "true"  -> return True
    "false" -> return False
    _ -> error "bool was neither true nor false"
