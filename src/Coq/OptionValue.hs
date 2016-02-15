{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Coq.OptionValue where

import Data.Aeson   (FromJSON, ToJSON)
import Data.Proxy
import GHC.Generics (Generic)
import Text.XML.Stream.Parse (tagName, requireAttr)

import FromXML
import ToXML

tagOptionValue :: ToXML a => String -> a -> String
tagOptionValue = mkTag "option_value"

data OptionValue
  = BoolValue   Bool
  | IntValue    (Maybe Int)
  | StringValue String
  deriving (Generic, Show)

instance FromJSON OptionValue

instance ToJSON OptionValue

instance FromXML OptionValue where
  instanceName Proxy = "OptionValue"
  parseXML = tagName "option_value" (requireAttr "val") $ \ val -> do
    case val of
      "boolvalue"   -> BoolValue   <$> forceXML
      "intvalue"    -> IntValue    <$> forceXML
      "stringvalue" -> StringValue <$> forceXML
      _ -> error "option_value was none of boolvalue, intvalue, stringvalue"

instance ToXML OptionValue where
  xml (BoolValue b)   = tagOptionValue "boolvalue"   b
  xml (IntValue i)    = tagOptionValue "intvalue"    i
  xml (StringValue s) = tagOptionValue "stringvalue" s
