{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Coq.CoqObject where

import Data.Aeson            (ToJSON)
import Data.Proxy
import GHC.Generics          (Generic)
import Text.XML.Stream.Parse (tagNoAttr)

import FromXML
import Utils

data CoqObject a
  = MkCoqObject [String] [String] a
  deriving (Generic)

instance ToJSON a => ToJSON (CoqObject a)

instance FromXML a => FromXML (CoqObject a) where
  instanceName Proxy = "CoqObject"
  parseXML = tagNoAttr "coq_object" $ do
    prefix <- forceXML
    qualId <- forceXML
    object <- forceXML
    return $ MkCoqObject prefix qualId object

instance Show a => Show (CoqObject a) where
  show (MkCoqObject modules names body) =
    "MkCoqObject " ++ sepBy "." modules ++ "." ++ sepBy "." names ++ " " ++ show body

instance {-# OVERLAPS #-} Show (CoqObject String) where
  show (MkCoqObject modules names body) =
    "MkCoqObject " ++ sepBy "." modules ++ "." ++ sepBy "." names ++ " " ++ body
