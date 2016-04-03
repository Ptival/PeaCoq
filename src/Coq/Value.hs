{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Coq.Value where

import Data.Aeson            (ToJSON)
import Data.Proxy
import GHC.Generics          (Generic)
import Text.XML.Stream.Parse (tagName)

import Coq.StateId
import FromXML
import Utils

type ErrorLocation = Maybe (Int, Int)

data Value a
  = ValueFail StateId ErrorLocation String
  | ValueGood a
  deriving (Generic, Show)

instance ToJSON a => ToJSON (Value a)

instance FromXML a => FromXML (Value a) where
  instanceName Proxy = "Value"
  parseXML =
    tagName "value"
    (do val <- unpackRequireAttr "val"
        locS <- castAttr "loc_s"
        locE <- castAttr "loc_e"
        return (val, locS, locE))
    $ \ (val, locS, locE) ->
    case val of
    "good" -> ValueGood <$> do
      forceXML
    "fail" -> do
      stateID <- forceXML
      errMsg <- unpackContent
      return $ ValueFail stateID (errorLoc locS locE) errMsg
    _ -> error $ "val was neither some nor none: " ++ val
    where
      errorLoc :: Maybe Int -> Maybe Int -> ErrorLocation
      errorLoc (Just s) (Just e) = Just (s, e)
      errorLoc _        _        = Nothing
