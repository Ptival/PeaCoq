{-# LANGUAGE OverloadedStrings #-}

module Handlers where

import           Control.Monad.Except
import           Control.Monad.Representable.Reader  (ask)
import           Data.Aeson
--import qualified Data.ByteString.Lazy                as BSL
import qualified Data.ByteString.UTF8                as BSU
import           Data.IORef
import qualified Data.IntMap                         as IM
import           Data.String.Utils                   (strip)
import qualified Data.Text                           as T
import           Prelude                             hiding (init)

import           Snap.Core
import           Snap.Extras.JSON
import           Snap.Snaplet
import           Snap.Snaplet.Session                hiding (touchSession)
import           Snap.Snaplet.Session.SessionManager ()
import           System.IO
--import           System.Log.Logger
import           System.Process
import           System.Random

import           Coq
import           PeaCoq
import           Session
import           XMLProtocol

lecturePath :: String
lecturePath = "web/coq/"

type PeaCoqHandler a = Handler PeaCoq PeaCoq a

{-
Wrap any input-needing 'MonadSnap' into an input-less one, gathering input
from the HTTP request.
-}
withParam :: (FromJSON i, MonadSnap m) => (i -> m o) -> m (Maybe o)
withParam k = do
  let paramName = "data"
  mp <- getParam paramName
  case mp of
    Nothing -> do
      liftIO . putStrLn $ "Failed to retrieve parameter: " ++ BSU.toString paramName
      return Nothing
    Just bs ->
      -- 'decode' only succeeds on lists and objects, use an artificial list...
      case decodeStrict (BSU.fromString ("[" ++ BSU.toString bs ++ "]")) of
      Just [i] -> Just <$> k i
      _ -> do
        liftIO . putStrLn $
          "Failed to JSON-parse the request parameter: " ++ BSU.toString bs
        return Nothing

{-
Run a 'CoqtopIO' as a 'PeaCoqHandler', gathering input from the HTTP request,
and returning output through the HTTP response.
-}
liftCoqtopIO :: (FromJSON i, ToJSON o) =>
               (i -> CoqtopIO o) -> (i -> PeaCoqHandler ())
liftCoqtopIO io i = do
  (SessionState _ hs st) <- getSessionState
  res@(_, st', _) <- liftIO . runCoqtopIO hs st $ io i
  setCoqState st'
  writeJSON res

handleCoqtopIO :: (FromJSON i, ToJSON o) =>
                 (i -> CoqtopIO o) -> PeaCoqHandler ()
handleCoqtopIO = void . withParam . liftCoqtopIO

startCoqtop :: String -> IO (Handle, Handle, Handle, ProcessHandle)
startCoqtop coqtop = do
  (hi, ho, he, ph) <- runInteractiveCommand coqtop
  hSetBuffering hi NoBuffering
  hSetBuffering ho NoBuffering
  hSetBuffering he NoBuffering
  --hInterp hi "Require Import Unicode.Utf8."
  --hForceValueResponse ho
  return (hi, ho, he, ph)

getGlobalState :: PeaCoqHandler GlobalState
getGlobalState = do
  globRef <- with lGlobRef ask
  liftIO $ readIORef globRef

modifyGlobalState :: (GlobalState -> (GlobalState, a)) -> PeaCoqHandler a
modifyGlobalState f = do
  globRef <- with lGlobRef ask
  liftIO $ atomicModifyIORef' globRef f

modifySessionState :: (SessionState -> (SessionState, a)) -> PeaCoqHandler a
modifySessionState f = do
  GlobalState { gActiveSessions = m, gCoqtop = coqtop } <- getGlobalState
  mapKey <- withSession lSession getSessionKey
  case IM.lookup mapKey m of
    Nothing -> do
      (hs, st) <- liftIO $ do
        hs <- startCoqtop coqtop
        (_, st, _) <- runCoqtopIO hs initialCoqState (init Nothing)
        return (hs, st)
      let (s, res) = f (SessionState True hs st)
      modifyGlobalState $ insertSession mapKey s
      --logAction hash $ "NEWSESSION " ++ show sessionIdentity
      return res
    Just s -> do
      -- update the timestamp
      let (s', res) = f s
      modifyGlobalState . adjustSession (touchSession . const s') $ mapKey
      return res

getSessionState :: PeaCoqHandler SessionState
getSessionState = modifySessionState (\ s -> (s, s))

setCoqState :: CoqState -> PeaCoqHandler ()
setCoqState s =
  modifySessionState (\ (SessionState a b _) -> (SessionState a b s, ()))

insertSession :: Int -> SessionState -> GlobalState -> (GlobalState, ())
insertSession mapKey s gs@(GlobalState { gNextSession = c, gActiveSessions = m }) =
  (gs { gNextSession = c + 1
      , gActiveSessions = IM.insert mapKey s m
      }, ())

--logAction :: String -> String -> IO ()
--logAction hash message = infoM rootLoggerName (hash ++ " " ++ message)

getGitCommitHash :: IO String
getGitCommitHash = strip <$> readProcess "git" ["rev-parse", "HEAD"] ""

getSessionKey :: PeaCoqHandler IM.Key
getSessionKey = with lSession $ do
  mkey <- getFromSession keyField
  case mkey of
    Nothing -> do
      key <- liftIO randomIO
      setInSession keyField (T.pack . show $ key)
      --liftIO . logAction $ "No session key found, initializing: " ++ show key
      return key
    Just key -> do
      --liftIO . logAction $ "Session key found: " ++ show key
      return . read . T.unpack $ key
  where
    keyField :: T.Text
    keyField = "key"

handlerAbout :: PeaCoqHandler ()
handlerAbout = handleCoqtopIO about

handlerAdd :: PeaCoqHandler ()
handlerAdd = handleCoqtopIO add

handlerAdd' :: PeaCoqHandler ()
handlerAdd' = handleCoqtopIO add'

handlerAnnotate :: PeaCoqHandler ()
handlerAnnotate = handleCoqtopIO annotate

handlerEditAt :: PeaCoqHandler ()
handlerEditAt = handleCoqtopIO editAt

handlerEvars :: PeaCoqHandler ()
handlerEvars = handleCoqtopIO evars

handlerGetOptions :: PeaCoqHandler ()
handlerGetOptions = handleCoqtopIO getOptions

handlerGoal :: PeaCoqHandler ()
handlerGoal = handleCoqtopIO goal

handlerHints :: PeaCoqHandler ()
handlerHints = handleCoqtopIO hints

handlerInit :: PeaCoqHandler ()
handlerInit = handleCoqtopIO init

handlerInterp :: PeaCoqHandler ()
handlerInterp = handleCoqtopIO interp

handlerMkCases :: PeaCoqHandler ()
handlerMkCases = handleCoqtopIO mkCases

handlerPrintAST :: PeaCoqHandler ()
handlerPrintAST = handleCoqtopIO printAST

handlerQuery :: PeaCoqHandler ()
handlerQuery = handleCoqtopIO query

handlerQuery' :: PeaCoqHandler ()
handlerQuery' = handleCoqtopIO query'

handlerQuit :: PeaCoqHandler ()
handlerQuit = handleCoqtopIO quit

handlerSearch :: PeaCoqHandler ()
handlerSearch = handleCoqtopIO search

handlerSetOptions :: PeaCoqHandler ()
handlerSetOptions = handleCoqtopIO setOptions

handlerStatus :: PeaCoqHandler ()
handlerStatus = handleCoqtopIO status

handlerStopWorker :: PeaCoqHandler ()
handlerStopWorker = handleCoqtopIO stopWorker

{-
logHandler :: HandlerInput -> PeaCoqHandler
logHandler input@(HandlerInput _ _ hash) = do
  param <- getParam "query"
  case param of
    Nothing -> return ()
    Just messageBS -> do
      let message = toString messageBS
      liftIO $ logAction hash message
      respond (Good ["OK"]) input

revisionHandler :: HandlerInput -> PeaCoqHandler
revisionHandler input@(HandlerInput _ _ serverHash) = do
  clientHash <- liftIO $ getGitCommitHash
  respond (Good [serverHash, clientHash]) input

listLecturesHandler :: HandlerInput -> PeaCoqHandler
listLecturesHandler input = do
  filePaths <- liftIO $ find always (extension ==? ".v") lecturePath
  -- don't want to show full path to users
  let files = map (drop (length lecturePath)) filePaths
  respond (Good files) input

loadLectureHandler :: HandlerInput -> PeaCoqHandler
loadLectureHandler input = do
  param <- getParam "query"
  case param of
    Nothing -> return ()
    Just messageBS -> do
      let fileName = toString messageBS
      contents <- liftIO $ readFile (lecturePath ++ fileName)
      respond (Good [contents]) input
-}
{-
identifyHandler :: IORef GlobalState -> HandlerInput -> PeaCoqHandler
identifyHandler ref input = do
  param <- getParam "query"
  case param of
    Nothing -> return ()
    Just payloadBS -> do
      let userId = toString payloadBS
      mapKey <- getSessionKey
      liftIO $ do
        handler <- fileHandler ("./log/log-" ++ userId) loggingPriority
        let format = simpleLogFormatter "[$time] $msg"
        let fHandler = setFormatter handler format
        updateGlobalLogger userId $ addHandler fHandler
        atomicModifyIORef' ref $ adjustSession (touchSession . setIdentity userId) mapKey
        noticeM userId $ "IDENTIFY " ++ show mapKey ++ " -> " ++ userId
      respond (Good ["OK"]) input
-}
