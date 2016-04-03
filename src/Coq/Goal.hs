{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Coq.Goal where

import Data.Aeson            (ToJSON)
import Data.Proxy
import GHC.Generics          (Generic)
import Text.XML.Stream.Parse (tagNoAttr)

import FromXML

data Goal
  = MkGoal String [String] String
  deriving (Generic, Show)

instance ToJSON Goal

instance FromXML Goal where
  instanceName Proxy = "Goal"
  parseXML = tagNoAttr "goal" $ do
    gid <- forceXML
    hyp <- forceXML
    ccl <- forceXML
    return $ MkGoal gid hyp ccl
