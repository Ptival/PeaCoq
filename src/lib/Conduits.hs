{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module Conduits where

import           Control.Monad.Catch      (MonadThrow)
import qualified Data.ByteString          as BS
import           Data.Conduit
import           Data.Conduit.Binary      (sourceHandle)
import           Data.XML.Types
import           System.IO
import           Text.XML
import           Text.XML.Stream.Parse    hiding (tag)

xmlConduit :: (MonadThrow m) => Conduit BS.ByteString m Event
xmlConduit = parseBytes $ def { psDecodeEntities = decodeHtmlEntities }

xmlConduitPos :: (MonadThrow m) => Conduit BS.ByteString m EventPos
xmlConduitPos = parseBytesPos $ def { psDecodeEntities = decodeHtmlEntities }

xmlSource :: Handle -> Producer IO Event
xmlSource h =
  yield ("<?xml version=\"1.0\" encoding=\"utf-8\"?>" :: BS.ByteString)
  =$= sourceHandle h
  $= xmlConduit

xmlSourcePos :: Handle -> Producer IO EventPos
xmlSourcePos h =
  yield ("<?xml version=\"1.0\" encoding=\"utf-8\"?>" :: BS.ByteString)
  =$= sourceHandle h
  $= xmlConduitPos
