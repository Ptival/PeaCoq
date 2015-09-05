{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module Coq where

import           Control.Monad.Catch      (MonadThrow)
import           Control.Monad.Loops      (whileM_)
import           Control.Monad.RWS.Strict
import           Data.Aeson               (FromJSON, ToJSON)
import qualified Data.ByteString          as BS
import           Data.Conduit
import           Data.Conduit.Binary      (sourceHandle)
import           Data.Either              (partitionEithers)
import           Data.List                (intersperse)
import           Data.Proxy
import           Data.Tree
import           Data.XML.Types
import           GHC.Generics             (Generic)
import           System.IO
import           System.Process           (ProcessHandle)
import           Text.XML
import           Text.XML.Stream.Parse    hiding (tag)

import           FromString
import           FromXML
import           ToXML
import           Utils

{-

A 'CoqIO':
- runs an 'IO' action
- can read input and output 'Handle'
- can write 'Message's and 'Feedback'
- can update a state with a state ID and an edit counter 'Int'
- may fail with result of type 'Fail'

-}

type Handles = (Handle, Handle, Handle, ProcessHandle)
type CoqReader = Handles
type CoqWriter = ([Message], [Feedback])
type CoqState = (StateId, Int)
type CoqIO = RWST CoqReader CoqWriter CoqState IO
type CoqtopIO a = CoqIO (Value a)

initialCoqState :: CoqState
initialCoqState = (StateId 1, 0) -- 1 after auto-initialization

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

data GXML a
  = Element String a [GXML a]
  | PCData String

type XML = GXML [(String, String)]

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

runCoqtopIO :: Handles -> CoqState -> CoqtopIO a -> IO (Value a, CoqState, CoqWriter)
runCoqtopIO hs st io = runRWST io' hs st
  where
    io' = do
      v <- io
      case v of
        -- when coqtop fails, it tells which state it is now in
        -- but apparently, 0 is a dummy value
        ValueFail (StateId 0) _ _ -> return ()
        ValueFail sid         _ _ -> setStateId sid
        ValueGood _ -> return ()
      return v

mkTag :: ToXML a => String -> String -> a -> String
mkTag name val contents =
  "<" ++ name ++ " val=\"" ++ val ++ "\">\n"
  ++ xml contents
  ++ "\n</" ++ name ++ ">"

hQuery :: (ToXML i) => String -> i -> CoqIO ()
hQuery cmd input = do
  (hi, _, _, _) <- ask
  let queryStr = mkTag "call" cmd input
  liftIO . putStrLn $ queryStr
  liftIO $ hPutStr hi queryStr
  return ()

instance FromXML FeedbackContent where
  instanceName Proxy = "FeedbackContent"
  parseXML = tagName "feedback_content" (unpackRequireAttr "val") $ \ val -> do
    case val of
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

hResponse :: forall a. (FromXML a, Show a) => CoqtopIO a
hResponse = do
  (_, ho, he, _) <- ask
  (messages, feedback, response) <- liftIO $ do

    -- flush stderr if needed
    -- TODO: report these errors
    whileM_ (hReady he) (hGetLine he)

    (resumable, messagesAndFeedback) <- xmlSource ho $$+ many parseXMLEither
    let (messages, feedback) = partitionEithers messagesAndFeedback
    (source, _) <- unwrapResumable resumable

    let messageStr = unlines . map show $ messages
    putStrLn $ "Message:\n" ++ take messageMaxLen messageStr
    if length messageStr > messageMaxLen
      then putStrLn "..."
      else return ()

    let feedbackStr = unlines . map show $ feedback
    putStrLn $ "Feedback:\n" ++ take feedbackMaxLen feedbackStr
    if length feedbackStr > feedbackMaxLen
      then putStrLn "..."
      else return ()

    response <- source $$ (forceXML :: Parser (Value a))
    putStrLn $ "Value: " ++ show response
    putStrLn $ replicate 60 '='
    return (messages, feedback, response)
  tell (messages, feedback)
  return response

hCall :: (ToXML i, FromXML o, Show o) => String -> i -> CoqtopIO o
hCall cmd input = do
  hQuery cmd input
  hResponse

hCallRawResponse :: (ToXML i) => String -> i -> CoqIO String
hCallRawResponse cmd input = do
  hQuery cmd input
  (_, ho, _, _) <- ask
  liftIO $ hGetContents ho

instance FromXML Status where
  instanceName Proxy = "Status"
  parseXML = tagNoAttr "status" $ do
    path <- forceXML
    proofName <- forceXML
    allProofs <- forceXML
    proofNum <- forceXML
    return $ MkStatus path proofName allProofs proofNum

xmlConduit :: (MonadThrow m) => Conduit BS.ByteString m Event
xmlConduit = parseBytes $ def { psDecodeEntities = decodeHtmlEntities }

xmlConduitPos :: (MonadThrow m) => Conduit BS.ByteString m EventPos
xmlConduitPos = parseBytesPos $ def { psDecodeEntities = decodeHtmlEntities }

xmlSource :: Handle -> Producer IO Event
xmlSource h =
  yield ("<?xml version=\"1.0\" encoding=\"utf-8\"?>" :: BS.ByteString)
  =$= sourceHandle h
  $= xmlConduit

xmlSourcePos :: Handle -> Producer IO EventPos
xmlSourcePos h =
  yield ("<?xml version=\"1.0\" encoding=\"utf-8\"?>" :: BS.ByteString)
  =$= sourceHandle h
  $= xmlConduitPos

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

getStateId :: CoqIO StateId
getStateId = gets fst

setStateId :: StateId -> CoqIO ()
setStateId sid = modify (\(_, eid) -> (sid, eid))

getNextEditId :: CoqIO Int
getNextEditId = do
  next <- gets snd
  return next

newEditID :: CoqIO Int
newEditID = do
  new <- gets snd
  modify (\(sid, _) -> (sid, new + 1))
  return new

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

data CoqXMLTag
  = Apply
  | Constant           String
  | Definition         String String
  | Gallina
  | Ltac               String
  | Operator
    String         -- name
    (Maybe String) -- kind
  | Proof
  | QED
  | Recurse
  | SectionSubsetDescr String
  | Theorem            String String
  | Token              String
  | Typed
  deriving (Generic)

instance ToJSON CoqXMLTag

type LocatedCoqXMLTag = (Maybe Location, CoqXMLTag)

instance {-# OVERLAPS #-} Show LocatedCoqXMLTag where
  show (Nothing, t)     = "[?-?] " ++ show t
  show (Just (b, e), t) = "[" ++ show b ++ "-" ++ show e ++ "] " ++ show t

type CoqXMLTree = Tree LocatedCoqXMLTag

instance Show CoqXMLTag where
  show Apply                  = "Apply"
  show (Constant s)           = "Constant " ++ s
  show (Definition a b)       = "Definition (" ++ a ++ ") " ++ b
  show Gallina                = "Gallina"
  show (Ltac s)               = "Ltac " ++ s
  show (Operator n mk)        = "Operator " ++ n ++ kind mk
    where
      kind :: Maybe String -> String
      kind Nothing  = ""
      kind (Just k) = " (kind = " ++ k ++ ")"
  show Proof                  = "Proof"
  show QED                    = "QED"
  show (SectionSubsetDescr a) = "SectionSubsetDescr " ++ a
  show Recurse                = "Recurse"
  show (Theorem a b)          = "Theorem (" ++ a ++ ") " ++ b
  show (Token s)              = "Token " ++ s
  show Typed                  = "Typed"

type Position = (Int, Int)

data PPXMLTag
  = Keyword String
  | PP String
  | VernacExpr String
  deriving (Generic)

instance Show PPXMLTag where
  show (Keyword s)     = "Keyword " ++ s
  show (PP s)          = "PP" ++ s
  show (VernacExpr s)  = "VernacExpr " ++ s

instance ToJSON PPXMLTag

type PositionedPPXMLTag = (Position, PPXMLTag)

type PPXMLTree = Tree (Either String PositionedPPXMLTag)

tagNameLoc :: Name -> AttrParser t ->
             (t -> Parser (CoqXMLTag, Forest LocatedCoqXMLTag)) ->
             ParseCoq
tagNameLoc name otherAttrs recur =
  tagName
  name
  (do b <- castRequireAttr "begin"
      e <- castRequireAttr "end"
      r <- otherAttrs
      return ((b, e), r)
  )
  (\ ((b, e), r) -> do
       (whichNode, contents) <- recur r
       return $ Node (Just (b, e), whichNode) contents
  )

tagNoAttrLoc :: Name -> Parser (CoqXMLTag, Forest LocatedCoqXMLTag) -> ParseCoq
tagNoAttrLoc name recur =
  tagNameLoc name (return ()) $ \ () -> recur

tagNamePos :: Name -> AttrParser t ->
             (t -> Parser (PPXMLTag, Forest (Either String PositionedPPXMLTag))) ->
             ParsePP
tagNamePos name otherAttrs recur =
  tagName
  name
  (do b <- castRequireAttr "startpos"
      e <- castRequireAttr "endpos"
      r <- otherAttrs
      return ((b, e), r)
  )
  (\ ((b, e), r) -> do
       (whichNode, contents) <- recur r
       return $ Node (Right ((b, e), whichNode)) contents
  )

tagNoAttrPos :: Name ->
               Parser (PPXMLTag, Forest (Either String PositionedPPXMLTag)) ->
               ParsePP
tagNoAttrPos name recur =
  tagNamePos name (return ()) $ \ () -> recur

instance {-# OVERLAPS #-} Show CoqXMLTree where
  show t = "\n" ++ drawTree (fmap show t)

type ParseCoq = Parser (Maybe CoqXMLTree)
type ForceCoq = Parser CoqXMLTree

type ParsePP = Parser (Maybe PPXMLTree)
type ForcePP = Parser PPXMLTree

parseOperator :: ParseCoq
parseOperator =
  tagNameLoc "operator"
  (do
       name <- unpackRequireAttr "name"
       kind <- unpackAttr "kind"
       return (name, kind)
  )
  $ \ (name, kind) -> do
    return (Operator name kind, [])

parseConstant :: ParseCoq
parseConstant =
  tagNameLoc "constant" (unpackRequireAttr "name") $ \ name -> do
    return (Constant name, [])

parseToken :: ParseCoq
parseToken =
  tagNoAttrLoc "token" $ do
    c <- unpackContent
    return (Token c, [])

parseTyped :: ParseCoq
parseTyped =
  tagNoAttrLoc "typed" $ do
    r <- many parseConstant
    return (Typed, r)

forceTyped :: ForceCoq
forceTyped = force "Typed" parseTyped

parseRecurse :: ParseCoq
parseRecurse =
  tagNoAttrLoc "recurse" $ do
    r <- many
        $ parseApply
        `orE` parseConstant
        `orE` parseToken
        `orE` parseTyped
    return (Recurse, r)

parseApply :: ParseCoq
parseApply =
  tagNoAttrLoc "apply" $ do
    r <- many $
        parseApply
        `orE` parseConstant
        `orE` parseOperator
        `orE` parseRecurse
        `orE` parseToken
        `orE` parseTyped
    return (Apply, r)

forceApply :: ForceCoq
forceApply = force "Apply" parseApply

parseTheorem :: ParseCoq
parseTheorem =
  tagNameLoc "theorem"
  (do ttype <- unpackRequireAttr "type"
      name  <- unpackRequireAttr "name"
      return (ttype, name))
  $ \ (ttype, name) -> do
    r <- many $
        parseApply
        `orE` parseConstant
    return (Theorem ttype name, r)

forceTheorem :: ForceCoq
forceTheorem = force "Theorem" parseTheorem

parseSectionSubestDescr :: ParseCoq
parseSectionSubestDescr =
  tagName "sectionsubsetdescr" (unpackRequireAttr "name") $ \ name ->
  return $ Node (Nothing, SectionSubsetDescr name) []

parseProof :: ParseCoq
parseProof = tagNoAttrLoc "proof" $ do
  r <- many parseSectionSubestDescr
  return (Proof, r)

forceProof :: ForceCoq
forceProof = force "Proof" parseProof

parseLtac :: ParseCoq
parseLtac = tagNoAttrLoc "ltac" $ do
  c <- unpackContent
  return (Ltac c, [])

parseQED :: ParseCoq
parseQED = tagNoAttrLoc "qed" (return (QED, []))

parseDefinition :: ParseCoq
parseDefinition =
  tagNameLoc "definition"
  (do
       ttype <- unpackRequireAttr "type"
       name  <- unpackRequireAttr "name"
       return (ttype, name)
   )
  $ \ (ttype, name) -> do
    r <- many $
        parseToken
    return (Definition ttype name, r)

parseGallina :: ParseCoq
parseGallina =
  tagNoAttrLoc "gallina" $ do
    r <- many $
        parseDefinition
        `orE` parseProof
        `orE` parseQED
        `orE` parseTheorem
    return (Gallina, r)

forceGallina :: ForceCoq
forceGallina = force "Gallina" parseGallina

instance FromXML CoqXMLTree where
  instanceName Proxy = "CoqXMLTree"
  parseXML = parseGallina `orE` parseLtac

parseKeyword :: ParsePP
parseKeyword = tagNoAttrPos "keyword" $ do
  c <- unpackContent
  return (Keyword c, [])

parseVernacExpr :: ParsePP
parseVernacExpr = tagNoAttrPos "vernac_expr" $ do
  r <- many $
      parseKeyword
  c <- unpackContent
  return (VernacExpr c, r)

instance FromXML PPXMLTree where
  instanceName Proxy = "PPXMLTree"
  parseXML = tagNoAttrPos "pp" $ do
    r <- many $
        parseVernacExpr
    c <- unpackContent
    return (PP c, r)
