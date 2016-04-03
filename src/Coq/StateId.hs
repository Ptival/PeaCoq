{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

module Coq.StateId where

import Data.Aeson            (FromJSON, ToJSON)
import Data.Proxy
import GHC.Generics          (Generic)
import Text.XML.Stream.Parse (tagName)

import FromString
import FromXML
import ToXML
import Utils

data StateId
  = StateId Int
  deriving (Generic, Show)

instance FromJSON StateId
instance ToJSON StateId

instance ToXML StateId where
  xml (StateId i) = "<state_id val=\"" ++ show i ++ "\"/>"

instance FromString StateId where
  fromString = StateId <$> read

instance FromXML StateId where
  instanceName Proxy = "StateId"
  parseXML = tagName "state_id" (castRequireAttr "val") $ \ val ->
    return $ StateId val
