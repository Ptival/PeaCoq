{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Coq.EditId where

import Data.Aeson            (ToJSON)
import Data.Proxy
import GHC.Generics          (Generic)
import Text.XML.Stream.Parse (tagName)

import FromXML
import Utils

data EditId
  = EditId Int
  deriving (Generic, Show)

instance ToJSON EditId

instance FromXML EditId where
  instanceName Proxy = "EditId"
  parseXML =
    tagName "edit_id"
    (do
         val <- castRequireAttr "val"
         return (EditId val))
    return
