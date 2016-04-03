{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

module Coq.Message where

import Data.Aeson            (ToJSON)
import Data.Proxy
import GHC.Generics          (Generic)
import Text.XML.Stream.Parse (tagNoAttr)

import Coq.MessageLevel
import FromXML

data Message
  = MkMessage MessageLevel String
  deriving (Generic)

instance Show Message where
  show (MkMessage level string) = "MkMessage " ++ show level ++ " " ++ string

instance ToJSON Message

instance FromXML Message where
  instanceName Proxy = "Message"
  parseXML =
    tagNoAttr "message" $ do
      level <- forceXML
      message <- forceXML
      return (MkMessage level message)
