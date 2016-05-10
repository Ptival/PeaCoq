{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

module Coq.Loc where

import Data.Aeson            (ToJSON)
import Data.Proxy
import GHC.Generics          (Generic)
import Text.XML.Stream.Parse (tagName)

import FromXML
import Utils

data Loc
  = MkLoc Int Int
  deriving (Generic, Show)

instance ToJSON Loc

instance FromXML Loc where
  instanceName Proxy = "Loc"
  parseXML =
    tagName "loc"
    (do start <- castRequireAttr "start"
        stop  <- castRequireAttr "stop"
        return (MkLoc start stop))
    return
