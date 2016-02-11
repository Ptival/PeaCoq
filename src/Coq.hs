{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Coq where

import           Data.Aeson               (FromJSON, ToJSON)

import           Data.List                (intersperse)
import           Data.Proxy
import           GHC.Generics             (Generic)
import           Text.XML.Stream.Parse    hiding (tag)

import           FromString
import           FromXML
import           ToXML
import           Utils

data StateId
  = StateId Int
  deriving (Generic, Show)

instance FromJSON StateId
instance ToJSON StateId

instance ToXML StateId where
  xml (StateId i) = "<state_id val=\"" ++ show i ++ "\"/>"

instance FromString StateId where
  fromString = StateId <$> read

data MessageLevel
  = Debug String
  | Error
  | Info
  | Notice
  | Warning
  deriving (Generic, Show)

instance ToJSON MessageLevel

data Message
  = MkMessage MessageLevel String
  deriving (Generic)

instance Show Message where
  show (MkMessage level string) = "MkMessage " ++ show level ++ " " ++ string

instance ToJSON Message

data Loc
  = MkLoc Int Int
  deriving (Generic, Show)

instance ToJSON Loc

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

data EditId
  = EditId Int
  deriving (Generic, Show)

instance ToJSON EditId

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

data Status =
  MkStatus [String] (Maybe String) [String] Int
  deriving (Generic, Show)

instance ToJSON Status

data Evar
  = MkEvar String
  deriving (Generic, Show)

instance ToJSON Evar

data Goal
  = MkGoal String [String] String
  deriving (Generic, Show)

instance ToJSON Goal

data PreGoal a
  = MkPreGoal [a] [([a], [a])] [a] [a]
  deriving (Generic, Show)

instance ToJSON a => ToJSON (PreGoal a)

data Goals
  = MkGoals (PreGoal Goal)
  deriving (Generic, Show)

instance ToJSON Goals

data OptionValue
  = BoolValue   Bool
  | IntValue    (Maybe Int)
  | StringValue String
  deriving (Generic, Show)

instance FromJSON OptionValue
instance ToJSON OptionValue

data OptionState
  = MkOptionState Bool Bool String OptionValue
  deriving (Generic, Show)

instance ToJSON OptionState

data CoqObject a
  = MkCoqObject [String] [String] a
  deriving (Generic)

instance ToJSON a => ToJSON (CoqObject a)

sepBy :: String -> [String] -> String
sepBy sep = concat . intersperse sep

instance Show a => Show (CoqObject a) where
  show (MkCoqObject modules names body) =
    "MkCoqObject " ++ sepBy "." modules ++ "." ++ sepBy "." names ++ " " ++ show body

instance {-# OVERLAPS #-} Show (CoqObject String) where
  show (MkCoqObject modules names body) =
    "MkCoqObject " ++ sepBy "." modules ++ "." ++ sepBy "." names ++ " " ++ body

data SearchConstraint
  = NamePattern String
  | TypePattern String
  | SubtypePattern String
  | InModule [String]
  | IncludeBlacklist
  deriving (Generic, Show)

instance FromJSON SearchConstraint

data CoqInfo
  = MkCoqInfo String String String String
  deriving (Generic)

instance Show CoqInfo where
  show (MkCoqInfo v d1 d2 d3) = "MkCoqInfo " ++ sepBy " " [v, d1, d2, d3]

instance ToJSON CoqInfo

{-
data GXML a
  = Element String a [GXML a]
  | PCData String

type XML = GXML [(String, String)]
-}

tagSearchConstraint :: ToXML a => String -> a -> String
tagSearchConstraint = mkTag "search_cst"

instance ToXML SearchConstraint where
  xml (NamePattern s)    = tagSearchConstraint "name_pattern"      s
  xml (TypePattern s)    = tagSearchConstraint "type_pattern"      s
  xml (SubtypePattern s) = tagSearchConstraint "subtype_pattern"   s
  xml (InModule l)       = tagSearchConstraint "in_module"         l
  xml IncludeBlacklist   = tagSearchConstraint "include_blacklist" ()

tagOptionValue :: ToXML a => String -> a -> String
tagOptionValue = mkTag "option_value"

instance ToXML OptionValue where
  xml (BoolValue b)   = tagOptionValue "boolvalue"   b
  xml (IntValue i)    = tagOptionValue "intvalue"    i
  xml (StringValue s) = tagOptionValue "stringvalue" s

mkTag :: ToXML a => String -> String -> a -> String
mkTag name val contents =
  "<" ++ name ++ " val=\"" ++ val ++ "\">\n"
  ++ xml contents
  ++ "\n</" ++ name ++ ">"

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
      _ -> error $ "Unknown feedback_content: " ++ val

instance FromXML EditId where
  instanceName Proxy = "EditId"
  parseXML =
    tagName "edit_id"
    (do
         val <- castRequireAttr "val"
         return (EditId val))
    return

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

instance FromXML MessageLevel where
  instanceName Proxy = "MessageLevel"
  parseXML =
    tagName "message_level" (unpackRequireAttr "val") $ \ val ->
    case val of
      "debug"   -> Debug <$> castContent
      "info"    -> return Info
      "notice"  -> return Notice
      "warning" -> return Warning
      "error"   -> return Error
      _ -> error $ "Unknown message_level: " ++ val

instance FromXML Message where
  instanceName Proxy = "Message"
  parseXML =
    tagNoAttr "message" $ do
      level <- forceXML
      message <- forceXML
      return (MkMessage level message)

messageMaxLen :: Int
messageMaxLen = 1000

feedbackMaxLen :: Int
feedbackMaxLen = 1000

parseXMLEither :: forall a b. (FromXML a, FromXML b) => Parser (Maybe (Either a b))
parseXMLEither =
        ((Left  <$>) <$> (parseXML :: Parser (Maybe a)))
  `orE` ((Right <$>) <$> (parseXML :: Parser (Maybe b)))

instance FromXML Status where
  instanceName Proxy = "Status"
  parseXML = tagNoAttr "status" $ do
    path <- forceXML
    proofName <- forceXML
    allProofs <- forceXML
    proofNum <- forceXML
    return $ MkStatus path proofName allProofs proofNum

instance FromXML StateId where
  instanceName Proxy = "StateId"
  parseXML = tagName "state_id" (castRequireAttr "val") $ \ val ->
    return $ StateId val

instance FromXML Loc where
  instanceName Proxy = "Loc"
  parseXML =
    tagName "loc"
    (do start <- castRequireAttr "start"
        stop  <- castRequireAttr "stop"
        return (MkLoc start stop))
    return

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

instance FromXML Evar where
  instanceName Proxy = "Evar"
  parseXML = tagNoAttr "evar" forceXML
  forceXML = force "forceXML failed: Evar" parseXML

instance FromXML Goal where
  instanceName Proxy = "Goal"
  parseXML = tagNoAttr "goal" $ do
    gid <- forceXML
    hyp <- forceXML
    ccl <- forceXML
    return $ MkGoal gid hyp ccl

instance FromXML Goals where
  instanceName Proxy = "Goals"
  parseXML = tagNoAttr "goals" $ do
    fgGoals <- forceXML
    bgGoals <- forceXML
    shelvedGoals <- forceXML
    givenUpGoals <- forceXML
    return $ MkGoals (MkPreGoal fgGoals bgGoals shelvedGoals givenUpGoals)

instance FromXML OptionValue where
  instanceName Proxy = "OptionValue"
  parseXML = tagName "option_value" (requireAttr "val") $ \ val -> do
    case val of
      "boolvalue"   -> BoolValue   <$> forceXML
      "intvalue"    -> IntValue    <$> forceXML
      "stringvalue" -> StringValue <$> forceXML
      _ -> error "option_value was none of boolvalue, intvalue, stringvalue"

instance FromXML OptionState where
  instanceName Proxy = "OptionState"
  parseXML = tagNoAttr "option_state" $ do
    sync <- forceXML
    depr <- forceXML
    name <- forceXML
    value <- forceXML
    return $ MkOptionState sync depr name value

instance FromXML a => FromXML (CoqObject a) where
  instanceName Proxy = "CoqObject"
  parseXML = tagNoAttr "coq_object" $ do
    prefix <- forceXML
    qualId <- forceXML
    object <- forceXML
    return $ MkCoqObject prefix qualId object

instance FromXML CoqInfo where
  instanceName Proxy = "CoqInfo"
  parseXML = tagNoAttr "coq_info" $ do
    coqtopVersion <- forceXML
    protocolVersion <- forceXML
    releaseDate <- forceXML
    compileDate <- forceXML
    return $ MkCoqInfo coqtopVersion protocolVersion releaseDate compileDate

type Location = (Int, Int)

type Position = (Int, Int)
