{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Coq.Feedback where

import Data.Aeson            (ToJSON)
import Data.Proxy
import GHC.Generics          (Generic)
import Text.XML.Stream.Parse (tagName)

import Coq.EditId
import Coq.FeedbackContent
import Coq.StateId
import FromXML
import Utils

data EditOrStateId
  = Edit EditId
  | State StateId
  deriving (Generic, Show)

instance ToJSON EditOrStateId

type RouteId = Int

data Feedback
  = MkFeedback EditOrStateId FeedbackContent RouteId
  deriving (Generic, Show)

instance ToJSON Feedback

instance FromXML Feedback where
  instanceName Proxy = "Feedback"
  parseXML =
    tagName "feedback"
    (do
         object <- unpackRequireAttr "object"
         route <- castRequireAttr "route"
         return (object, route))
    $ \ (object, route) -> do
      editOrStateId <- case object of
        "edit" -> Edit <$> forceXML
        "state" -> State <$> forceXML
        _ -> error "feedback object was neither edit nor state"
      feedbackContent <- forceXML
      return $ MkFeedback editOrStateId feedbackContent route
