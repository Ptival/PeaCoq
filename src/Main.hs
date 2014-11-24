{-# LANGUAGE OverloadedStrings #-}

module Main where

import           Control.Applicative ((<$>))
import           Control.Concurrent (forkIO, threadDelay)
import           Control.Monad (forever, forM)
import           Control.Monad.IO.Class (liftIO)
import           Data.ByteString (ByteString, append)
import           Data.ByteString.UTF8 (toString)
import qualified Data.HashMap.Strict as HM (map)
import           Data.IORef
import qualified Data.IntMap as IM
import qualified Data.Text as T
import           Data.Time.LocalTime (getZonedTime)
import           Prelude hiding (log)
import           Snap.Core
import           Snap.Extras.JSON
import           Snap.Http.Server.Config (defaultConfig)
import           Snap.Snaplet
import           Snap.Snaplet.Session hiding (touchSession)
import           Snap.Snaplet.Session.Backends.CookieSession (initCookieSessionManager)
import           Snap.Snaplet.Session.SessionManager ()
import           Snap.Util.FileServe
import           System.IO
import           System.Log.Formatter
import           System.Log.Handler (setFormatter)
import           System.Log.Handler.Simple
import           System.Log.Logger
import           System.Process
import           System.Random

import           CoqTypes
import           Coqtop
import           Parser
import           PeaCoq

data GlobalState
  = GlobalState
    Int                      -- next session number
    (IM.IntMap SessionState) -- active sessions

data SessionState
  = SessionState
    Int              -- an identifier for the session
    Bool             -- True while the session is alive
    (Handle, Handle) -- I/O handles
    ProcessHandle    -- useful to kill the process

type PeaCoqHandler = Handler PeaCoq PeaCoq ()

data HandlerInput = HandlerInput
  { identifier :: String
  , inputHandle :: Handle
  , outputHandle :: Handle
  }

sessionTimeoutSeconds :: Int
sessionTimeoutSeconds = 3600

sessionTimeoutMicroseconds :: Int
sessionTimeoutMicroseconds = sessionTimeoutSeconds * 1000 * 1000

loggingPriority :: Priority
loggingPriority = INFO

logAction :: String -> String -> IO ()
logAction = infoM

main :: IO ()
main = do
  updateGlobalLogger rootLoggerName (setLevel loggingPriority)
  globRef <- newIORef $ GlobalState 0 IM.empty
  forkIO $ cleanStaleSessions globRef -- parallel thread to regularly clean up
  serveSnaplet defaultConfig $ peacoqSnaplet globRef

log :: String -> IO ()
log m = do
  t <- getZonedTime
  putStrLn $ show t ++ ": " ++ m

isAlive :: SessionState -> Bool
isAlive (SessionState _ alive _ _) = alive

markStale :: SessionState -> SessionState
markStale (SessionState n _ h ph) = SessionState n False h ph

touchSession :: SessionState -> SessionState
touchSession (SessionState n _ h ph) = SessionState n True h ph

cleanStaleSessions :: IORef GlobalState -> IO ()
cleanStaleSessions globRef = forever $ do
  sessionsToClose <- atomicModifyIORef' globRef markAndSweep
  forM sessionsToClose $ \(SessionState ident _ (hi, ho) ph) -> do
    logAction (show ident) $ "END SESSION"
    log $ "Terminating coqtop session " ++ show ident
    hClose hi
    hClose ho
    terminateProcess ph -- not stricly necessary
    waitForProcess ph
  threadDelay sessionTimeoutMicroseconds
  where
    markAndSweep :: GlobalState -> (GlobalState, [SessionState])
    markAndSweep (GlobalState c m) =
      let (alive, stale) = IM.partition isAlive m in
      (GlobalState c (IM.map markStale alive), IM.elems stale)

startCoqtop :: IO (Handle, Handle, ProcessHandle)
startCoqtop = do
  (hi, ho, he, ph) <- runInteractiveCommand "coqtop -ideslave"
  hClose he
  hSetBinaryMode hi False
  hSetBuffering stdin LineBuffering
  hSetBuffering hi NoBuffering
  hInterp hi "Require Import Unicode.Utf8."
  hForceValueResponse ho
  return (hi, ho, ph)

sessionKey :: T.Text
sessionKey = "key"

withSessionHandles ::
  IORef GlobalState
  -> (HandlerInput -> PeaCoqHandler)
  -> PeaCoqHandler
withSessionHandles r h = withSession lSession $ do
  -- retrieve or create a key for this session
  mapKey <- with lSession $ do
    mkey <- getFromSession sessionKey
    case mkey of
      Nothing -> do
        key <- liftIO randomIO
        setInSession sessionKey (T.pack . show $ key)
        return key
      Just key -> do
        return . read . T.unpack $ key
  -- retrieve or create two handles for this session
  (ident, hi, ho) <- liftIO $ do
    GlobalState _ m <- readIORef r
    case IM.lookup mapKey m of
      Nothing -> do
        (hi, ho, ph) <- startCoqtop
        n <- atomicModifyIORef' r $ updateNewSession mapKey (hi, ho) ph
        let ident = show n
        handler <- fileHandler ("./log/log-" ++ ident) loggingPriority
        let format = simpleLogFormatter "[$time] $msg"
        let fHandler = setFormatter handler format
        updateGlobalLogger ident $ addHandler fHandler
        logAction ident "NEW SESSION"
        log $ "Starting coqtop session " ++ show n
        return (n, hi, ho)
      Just (SessionState ident _ (hi, ho) _) -> do
        -- update the timestamp
        atomicModifyIORef' r $ updateTouchSession mapKey
        return (ident, hi, ho)
  -- run the handler
  h (HandlerInput (show ident) hi ho)
  where
    updateNewSession
      :: Int -> (Handle, Handle) -> ProcessHandle -> GlobalState -> (GlobalState, Int)
    updateNewSession mapKey hs ph (GlobalState c m) =
      (GlobalState (c + 1) (IM.insert mapKey (SessionState c True hs ph) m), c)
    updateTouchSession :: Int -> GlobalState -> (GlobalState, Int)
    updateTouchSession mapKey (GlobalState c m) =
      (GlobalState c (IM.adjust touchSession mapKey m), c)

peacoqSnaplet :: IORef GlobalState -> SnapletInit PeaCoq PeaCoq
peacoqSnaplet globRef = makeSnaplet "PeaCoq" "PeaCoq" Nothing $ do
  s <- nestSnaplet "session" lSession cookieSessionManager
  addRoutes peacoqRoutes
  return $ PeaCoq s
  where
    cookieSessionManager :: SnapletInit PeaCoq SessionManager
    cookieSessionManager = initCookieSessionManager "encryption_key" "peacoq_session" Nothing
    myDirConfig :: DirectoryConfig (Handler PeaCoq PeaCoq)
    myDirConfig =
      defaultDirectoryConfig {
        mimeTypes = HM.map (\m -> append m "; charset=utf-8") defaultMimeTypes
        }
    peacoqRoutes :: [(ByteString, PeaCoqHandler)]
    peacoqRoutes =
      map (\(r, handler) -> (r, withSessionHandles globRef handler))
      [ ("log",              logHandler)
      , ("query",            queryHandler)
      , ("queryundo",        queryUndoHandler)
      , ("undo",             undoHandler)
      , ("status",           statusHandler)
      , ("rewind",           rewindHandler)
      , ("qed",              qedHandler)
      , ("setprintingall",   togglePrintingAll True)
      , ("unsetprintingall", togglePrintingAll False)
      , ("parse",            parseHandler)
      , ("parseEval",        parseEvalHandler)
      ] ++
      [ ("/",                serveDirectoryWith myDirConfig "web/")
      ]

respond :: CoqtopResponse [String] -> HandlerInput -> PeaCoqHandler
respond response (HandlerInput _ hi ho) = do
  goals <- liftIO $ hQueryGoal hi ho
  writeJSON $ MkPeaCoqResponse goals response

parseHandler :: HandlerInput -> PeaCoqHandler
parseHandler _ = do
  param <- getParam "query"
  case param of
    Nothing -> return ()
    Just queryBS -> do
      let response = parseVernac $ toString queryBS
      writeJSON response

parseEvalHandler :: HandlerInput -> PeaCoqHandler
parseEvalHandler _ = do
  param <- getParam "query"
  case param of
    Nothing -> return ()
    Just queryBS -> do
      let response = parseEval $ toString queryBS
      writeJSON response

queryHandler :: HandlerInput -> PeaCoqHandler
queryHandler input@(HandlerInput _ hi ho) = do
  param <- getParam "query"
  case param of
    Nothing -> return ()
    Just queryBS -> do
      response <- liftIO $ do
        -- might want to sanitize? :3
        let query = toString queryBS
        putStrLn $ query
        hInterp hi query
        hForceValueResponse ho
      respond response input

queryUndoHandler :: HandlerInput -> PeaCoqHandler
queryUndoHandler input@(HandlerInput _ hi ho) = do
  param <- getParam "query"
  case param of
    Nothing -> return ()
    Just queryBS -> do
      response <- liftIO $ do
        -- might want to sanitize? :3
        let query = toString queryBS
        hInterp hi query
        hForceValueResponse ho
      respond response input
      case response of
        Fail _ ->
          return ()
        Good _ ->
          do
            liftIO $ hCall hi [("val", "rewind"), ("steps", "1")] ""
            liftIO $ hForceValueResponse ho
            return ()

undoHandler :: HandlerInput -> PeaCoqHandler
undoHandler input@(HandlerInput _ hi ho) = do
  liftIO $ hCall hi [("val", "rewind"), ("steps", "1")] ""
  r <- liftIO $ hForceValueResponse ho
  respond r input

statusHandler :: HandlerInput -> PeaCoqHandler
statusHandler input@(HandlerInput _ hi ho) = do
  liftIO $ hCall hi [("val", "status")] ""
  r <- liftIO $ hForceStatusResponse ho
  respond (return . show <$> r) input

rewindHandler :: HandlerInput -> PeaCoqHandler
rewindHandler input@(HandlerInput _ hi ho) = do
  param <- getParam "query"
  case param of
    Nothing -> return ()
    Just stepsBS -> do
      liftIO $ hCall hi [("val", "rewind"), ("steps", toString stepsBS)] ""
      r <- liftIO $ hForceValueResponse ho
      respond (return . show <$> r) input

qedHandler :: HandlerInput -> PeaCoqHandler
qedHandler input@(HandlerInput _ hi ho) = do
  liftIO $ hInterp hi "Qed."
  r <- liftIO $ hForceValueResponse ho
  respond r input

togglePrintingAll :: Bool -> HandlerInput -> PeaCoqHandler
togglePrintingAll b input@(HandlerInput _ hi ho) = do
  let query =
        "<call id=\"0\" val=\"setoptions\">"
        ++ "<pair><list><string>Printing</string><string>All</string></list>"
        ++ "<option_value val=\"boolvalue\"><bool val=\""
        ++ (if b then "true" else "false")
        ++ "\"></bool></option_value>"
        ++ "</pair></call>"
  liftIO $ hPutStrLn hi query
  r <- liftIO $ hForceValueResponse ho
  respond r input

logHandler :: HandlerInput -> PeaCoqHandler
logHandler input@(HandlerInput ident _ _) = do
  param <- getParam "query"
  case param of
    Nothing -> return ()
    Just messageBS -> do
      let message = toString messageBS
      liftIO . putStrLn $ "Attempting to log: " ++ message
      liftIO $ noticeM ident message
      respond (Good ["OK"]) input
