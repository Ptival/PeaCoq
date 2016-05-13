{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Coq.Goals where

import Data.Aeson            (ToJSON)
import Data.Proxy
import GHC.Generics          (Generic)
import Text.XML.Stream.Parse (tagNoAttr)

import Coq.Goal
import FromXML

data PreGoal a
  = MkPreGoal [a] [([a], [a])] [a] [a]
  deriving (Generic, Show)

instance ToJSON a => ToJSON (PreGoal a)

data Goals
  = MkGoals (PreGoal Goal)
  deriving (Generic, Show)

instance ToJSON Goals

instance FromXML Goals where
  instanceName Proxy = "Goals"
  parseXML = tagNoAttr "goals" $ do
    fgGoals <- forceXML
    bgGoals <- forceXML
    shelvedGoals <- forceXML
    givenUpGoals <- forceXML
    return $ MkGoals (MkPreGoal fgGoals bgGoals shelvedGoals givenUpGoals)
