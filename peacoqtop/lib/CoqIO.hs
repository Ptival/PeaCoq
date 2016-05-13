{-# LANGUAGE RankNTypes #-}

module CoqIO where

import Control.Monad.Loops      (whileM_)
import Control.Monad.RWS.Strict
import Data.Conduit
import Data.Either              (partitionEithers)
import System.IO
import Text.XML.Stream.Parse    hiding (tag)
import System.Process           (ProcessHandle)

import Conduits
import Coq
import FromXML
import ToXML

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

initialCoqState :: CoqState
initialCoqState = (StateId 1, 0) -- 1 after auto-initialization

type CoqIO = RWST CoqReader CoqWriter CoqState IO
type CoqtopIO a = CoqIO (Value a)

hResponseDebug :: String -> IO ()
hResponseDebug s = if True then putStrLn s else return ()

messageMaxLen :: Int
messageMaxLen = 1000

feedbackMaxLen :: Int
feedbackMaxLen = 1000

parseXMLEither :: (FromXML a, FromXML b) => Parser (Maybe (Either a b))
--parseXMLEither :: forall a b. (FromXML a, FromXML b) => Parser (Maybe (Either a b))
parseXMLEither =
        ((Left  <$>) <$> parseXML)
  `orE` ((Right <$>) <$> parseXML)

hResponse :: forall a. (FromXML a, Show a) => CoqtopIO a
hResponse = do
  (_, ho, he, _) <- ask
  (messages, feedback, response) <- liftIO $ do

    -- flush stderr if needed
    -- TODO: report these errors
    whileM_ (hReady he) $ hGetLine he >>= putStrLn

    (resumable, messagesAndFeedback) <- xmlSource ho $$+ many parseXMLEither
    let (messages, feedback) = partitionEithers messagesAndFeedback
    (source, _) <- unwrapResumable resumable

    let messageStr = unlines . map show $ messages
    hResponseDebug $ "Message:\n" ++ take messageMaxLen messageStr
    if length messageStr > messageMaxLen
      then putStrLn "..."
      else return ()

    let feedbackStr = unlines . map show $ feedback
    hResponseDebug $ "Feedback (" ++ show (length feedback) ++"):\n" ++ take feedbackMaxLen feedbackStr
    if length feedbackStr > feedbackMaxLen
      then putStrLn "..."
      else return ()

    response <- source $$ (forceXML :: (FromXML a) => Parser (Value a))
    hResponseDebug $ "Value: " ++ show response
    hResponseDebug $ replicate 60 '='

    return (messages, feedback, response)
  tell (messages, feedback)
  setStateIdFromValue response
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

hQuery :: (ToXML i) => String -> i -> CoqIO ()
hQuery cmd input = do
  (hi, _, _, _) <- ask
  let queryStr = mkTag "call" cmd input
  liftIO . putStrLn $ queryStr
  liftIO $ hPutStr hi queryStr
  return ()

-- when coqtop fails, it tells which state it is now in
-- but apparently, 0 is a dummy value
setStateIdFromValue :: Value a -> CoqIO ()
setStateIdFromValue (ValueFail (StateId 0) _ _) = return ()
-- apparently, backtracking to this sid make coqtop unhappy
setStateIdFromValue (ValueFail _sid        _ _) = return () --setStateId sid
setStateIdFromValue (ValueGood _)               = return ()

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

runCoqtopIO :: Handles -> CoqState -> CoqtopIO a -> IO (Value a, CoqState, CoqWriter)
runCoqtopIO hs st io = runRWST io' hs st
  where
    io' = do
      v <- io
      setStateIdFromValue v
      return v
