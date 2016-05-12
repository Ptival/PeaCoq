{-# LANGUAGE OverloadedStrings #-}

module PeaCoqHandler where

import           Control.Monad.Except
import           Control.Monad.Representable.Reader  (ask)
import           Data.Aeson
import qualified Data.ByteString.UTF8                as BSU
import           Data.IORef
import qualified Data.IntMap                         as IM
import qualified Data.Text                           as T
import           Prelude                             hiding (init)

import           Snap.Core
import           Snap.Extras.JSON
import           Snap.Snaplet
import           Snap.Snaplet.Session                hiding (touchSession)
import           Snap.Snaplet.Session.SessionManager ()
import           System.Directory                    (doesFileExist)
import           System.IO
import           System.Process
import           System.Random

import           CoqIO
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
getGitCommitHash = do
  -- let's not use git to be more portable
  --strip <$> readProcess "git" ["rev-parse", "HEAD"] ""
  let fileName = ".git/refs/heads/master"
  b <- doesFileExist fileName
  if b
  then readFile fileName
  else return "Commit # unavailable"

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
