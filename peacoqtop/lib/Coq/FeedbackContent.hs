{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

module Coq.FeedbackContent where

import Data.Aeson            (ToJSON)
import Data.Proxy
import GHC.Generics          (Generic)
import Text.XML.Stream.Parse (tagName)

import Coq.Loc
import Coq.Message
import FromXML
import Utils

data FeedbackContent
  = AddedAxiom
  | Complete
  | Custom Loc String () -- TODO: xml
  | ErrorMsg Loc String
  | FileDependency (Maybe String) String
  | FileLoaded String String
  | GlobDef Loc String String String
  | GlobRef Loc String String String String
  | Goals Loc String
  | Incomplete
  | InProgress
  | Message Message
  | Processed
  | ProcessingIn String
  | WorkerStatus String String
  deriving (Generic, Show)

instance ToJSON FeedbackContent

instance FromXML FeedbackContent where
  instanceName Proxy = "FeedbackContent"
  parseXML = tagName "feedback_content" (unpackRequireAttr "val") $ \ val -> do
    case val of
      "addedaxiom" ->
        return AddedAxiom
      "complete" ->
        return Complete
      "errormsg" -> do
        loc <- forceXML
        err <- forceXML
        return $ ErrorMsg loc err
      "filedependency" -> do
        from <- forceXML
        dep <- forceXML
        return $ FileDependency from dep
      "fileloaded" -> do
        dirPath <- forceXML
        fileName <- forceXML
        return $ FileLoaded dirPath fileName
      "processed" ->
        return Processed
      "processingin" ->
        ProcessingIn <$> forceXML
      "workerstatus" -> do
        workerId <- forceXML
        status <- forceXML
        return $ WorkerStatus workerId status
      _ -> error $ "Unknown feedback_content: " ++ val
