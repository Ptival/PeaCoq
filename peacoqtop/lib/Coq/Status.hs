{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Coq.Status where

import Data.Aeson            (ToJSON)
import Data.Proxy
import GHC.Generics          (Generic)
import Text.XML.Stream.Parse (tagNoAttr)

import FromXML

data Status =
  MkStatus [String] (Maybe String) [String] Int
  deriving (Generic, Show)

instance ToJSON Status

instance FromXML Status where
  instanceName Proxy = "Status"
  parseXML = tagNoAttr "status" $ do
    path <- forceXML
    proofName <- forceXML
    allProofs <- forceXML
    proofNum <- forceXML
    return $ MkStatus path proofName allProofs proofNum
