module Utils where

import           Control.Monad.Catch   (MonadThrow)
import           Data.Conduit          (Consumer)
import qualified Data.Text             as T
import           Data.XML.Types        (Event, Name)
import           Text.XML.Stream.Parse

import FromString

{- Unpacking and casting -}

readUnpack :: (FromString a) => T.Text -> a
readUnpack = fromString . T.unpack

unpackRequireAttr :: Name -> AttrParser String
unpackRequireAttr s = T.unpack <$> requireAttr s

castRequireAttr :: (FromString a) => Name -> AttrParser a
castRequireAttr s = readUnpack <$> requireAttr s

unpackAttr :: Name -> AttrParser (Maybe String)
unpackAttr s = (T.unpack <$>) <$> attr s

castAttr :: (FromString a) => Name -> AttrParser (Maybe a)
castAttr s = (readUnpack <$>) <$> attr s

unpackContent :: (MonadThrow m) => Consumer Event m String
unpackContent = T.unpack <$> content

castContent :: (FromString a, MonadThrow m) => Consumer Event m a
castContent = readUnpack <$> content
