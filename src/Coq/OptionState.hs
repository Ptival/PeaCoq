{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Coq.OptionState where

import Data.Aeson            (ToJSON)
import Data.Proxy
import GHC.Generics          (Generic)
import Text.XML.Stream.Parse (tagNoAttr)

import Coq.OptionValue
import FromXML

data OptionState
  = MkOptionState Bool Bool String OptionValue
  deriving (Generic, Show)

instance ToJSON OptionState

instance FromXML OptionState where
  instanceName Proxy = "OptionState"
  parseXML = tagNoAttr "option_state" $ do
    sync <- forceXML
    depr <- forceXML
    name <- forceXML
    value <- forceXML
    return $ MkOptionState sync depr name value
