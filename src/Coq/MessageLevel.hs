{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

module Coq.MessageLevel where

import Data.Aeson            (ToJSON)
import Data.Proxy
import GHC.Generics          (Generic)
import Text.XML.Stream.Parse (tagName)

import FromXML
import Utils

data MessageLevel
  = Debug String
  | Error
  | Info
  | Notice
  | Warning
  deriving (Generic, Show)

instance ToJSON MessageLevel

instance FromXML MessageLevel where
  instanceName Proxy = "MessageLevel"
  parseXML =
    tagName "message_level" (unpackRequireAttr "val") $ \ val ->
    case val of
      "debug"   -> Debug <$> castContent
      "info"    -> return Info
      "notice"  -> return Notice
      "warning" -> return Warning
      "error"   -> return Error
      _ -> error $ "Unknown message_level: " ++ val
