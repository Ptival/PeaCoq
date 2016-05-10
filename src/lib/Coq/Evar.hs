{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Coq.Evar where

import Data.Aeson            (ToJSON)
import Data.Proxy
import GHC.Generics          (Generic)
import Text.XML.Stream.Parse (force, tagNoAttr)

import FromXML

data Evar
  = MkEvar String
  deriving (Generic, Show)

instance ToJSON Evar

instance FromXML Evar where
  instanceName Proxy = "Evar"
  parseXML = tagNoAttr "evar" forceXML
  forceXML = force "forceXML failed: Evar" parseXML
