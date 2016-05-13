{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Coq.CoqInfo where

import Data.Aeson            (ToJSON)
import Data.Proxy
import GHC.Generics          (Generic)
import Text.XML.Stream.Parse (tagNoAttr)

import FromXML
import Utils

data CoqInfo
  = MkCoqInfo String String String String
  deriving (Generic)

instance Show CoqInfo where
  show (MkCoqInfo v d1 d2 d3) = "MkCoqInfo " ++ sepBy " " [v, d1, d2, d3]

instance ToJSON CoqInfo

instance FromXML CoqInfo where
  instanceName Proxy = "CoqInfo"
  parseXML = tagNoAttr "coq_info" $ do
    coqtopVersion <- forceXML
    protocolVersion <- forceXML
    releaseDate <- forceXML
    compileDate <- forceXML
    return $ MkCoqInfo coqtopVersion protocolVersion releaseDate compileDate
