
{-# LANGUAGE OverloadedStrings #-}

module Main where

import           Control.Applicative ((<$>))
import           Control.Concurrent (forkIO, threadDelay)
import           Control.Monad (forever, forM)
import           Control.Monad.IO.Class (liftIO)
import           Data.ByteString (ByteString, append)
import qualified Data.HashMap.Strict as HM (map)
import           Data.IORef
import qualified Data.IntMap as IM
import           Data.Time.Format
import           Data.Time.LocalTime
import           Network.Socket
import           Prelude hiding (log)
import           Snap.Core (MonadSnap)
import           Snap.Http.Server.Config
import           Snap.Snaplet
import           Snap.Snaplet.Session hiding (touchSession)
import           Snap.Snaplet.Session.Backends.CookieSession (initCookieSessionManager)
import           Snap.Snaplet.Session.SessionManager ()
import           Snap.Util.FileServe
import           System.Directory
import           System.IO
import           System.Locale
import           System.Log.Formatter
import           System.Log.Handler (setFormatter)
import           System.Log.Handler.Simple
import           System.Log.Logger
import           System.Process

import           Coqtop
import           Handlers
import           PeaCoq
import           Session

configFile :: FilePath
configFile = ".PeaCoqConfig.hs"

data GlobalState
  = GlobalState
    Int                      -- next session number
    (IM.IntMap SessionState) -- active sessions
    (Maybe String)           -- user name

main :: IO ()
main = mainUW

{-
mainWeb :: IO ()
mainWeb =do
  updateGlobalLogger rootLoggerName (setLevel loggingPriority)
  globRef <- newIORef $ GlobalState 0 IM.empty
  forkIO $ cleanStaleSessions globRef -- parallel thread to regularly clean up
  serveSnaplet defaultConfig $ peacoqSnaplet globRef
-}

data PeaCoqConfig =
  PeaCoqConfig
  { configUserId  :: Maybe String
  , configLogPath :: FilePath
  }
  deriving (Read)

serverConfig :: MonadSnap m => FilePath -> Maybe String -> String -> Config m a
serverConfig logPath mUserId nowString =
  setStartupHook hook -- this hook will figure out which port was used and print it
  . setPort 0 -- 0 means that unless specified, pick a random port
  . setAccessLog (ConfigFileLog $ prefix mUserId ++ "access.log")
  . setErrorLog (ConfigFileLog $ prefix mUserId ++ "error.log")
  $ defaultConfig
  where
    prefix (Just userId) = logPath ++ "/" ++ userId ++ nowString ++ "-"
    prefix Nothing       = logPath ++ "/" ++ nowString ++ "-"
    hook dat = do
      port <- socketPort . head $ getStartupSockets dat
      putStrLn $ "Server listening on port: " ++ show port
      putStrLn $ "On recycle, visit: http://recycle.cs.washington.edu:" ++ show port
      putStrLn $ "On attu, visit: http://attu.cs.washington.edu:" ++ show port
      putStrLn $ "Otherwise, visit: http://localhost:" ++ show port

{-
For running the UW study, each participant will run their own instance of the server.
-}
mainUW :: IO ()
mainUW = do
  homeDir <- getHomeDirectory
  PeaCoqConfig mUserId logPath <- read <$> readFile (homeDir ++ "/" ++ configFile)
  now <- getZonedTime
  let nowString = formatTime defaultTimeLocale "-%F-%H-%M-%S" now
  case mUserId of
    Just userId -> do
      handler <- fileHandler (logPath ++ "/" ++ userId ++ nowString ++ ".log") loggingPriority
      let format = simpleLogFormatter "[$time] $msg"
      let fHandler = setFormatter handler format
      updateGlobalLogger rootLoggerName (setLevel loggingPriority . addHandler fHandler)
      logAction $ "USERIDENTIFIED " ++ userId
    Nothing -> return ()
  globRef <- newIORef $ GlobalState 0 IM.empty mUserId
  forkIO $ cleanStaleSessions globRef -- parallel thread to regularly clean up
  serveSnaplet (serverConfig logPath mUserId nowString) $ peacoqSnaplet globRef

sessionTimeoutSeconds :: Int
sessionTimeoutSeconds = 24 * 3600

sessionTimeoutMicroseconds :: Int
sessionTimeoutMicroseconds = sessionTimeoutSeconds * 1000 * 1000

loggingPriority :: Priority
loggingPriority = INFO

closeSession :: SessionState -> IO ()
closeSession (SessionState sessId _ (hi, ho) ph) = do
  logAction $ "END SESSION " ++ show sessId
  hClose hi
  hClose ho
  terminateProcess ph -- not stricly necessary
  waitForProcess ph
  return ()

cleanStaleSessions :: IORef GlobalState -> IO ()
cleanStaleSessions globRef = forever $ do
  sessionsToClose <- atomicModifyIORef' globRef markAndSweep
  forM sessionsToClose closeSession
  threadDelay sessionTimeoutMicroseconds
  where
    markAndSweep :: GlobalState -> (GlobalState, [SessionState])
    markAndSweep (GlobalState c m u) =
      let (alive, stale) = IM.partition isAlive m in
      (GlobalState c (IM.map markStale alive) u, IM.elems stale)

startCoqtop :: IO (Handle, Handle, ProcessHandle)
startCoqtop = do
  (hi, ho, he, ph) <- runInteractiveCommand "coqtop -ideslave"
  hClose he
  hSetBinaryMode hi False
  hSetBuffering stdin LineBuffering
  hSetBuffering hi NoBuffering
  --hInterp hi "Require Import Unicode.Utf8."
  --hForceValueResponse ho
  return (hi, ho, ph)

withSessionHandles ::
  IORef GlobalState
  -> (HandlerInput -> PeaCoqHandler)
  -> PeaCoqHandler
withSessionHandles r h = withSession lSession $ do
  -- retrieve or create a key for this session
  mapKey <- getSessionKey
  -- retrieve or create two handles for this session
  (hi, ho) <- liftIO $ do
    GlobalState _ m _ <- readIORef r
    case IM.lookup mapKey m of
      Nothing -> do
        (hi, ho, ph) <- startCoqtop
        sessionIdentity <- atomicModifyIORef' r $ updateNewSession mapKey (hi, ho) ph
        logAction $ "NEWSESSION " ++ show sessionIdentity
        return (hi, ho)
      Just (SessionState _ _ (hi, ho) _) -> do
        -- update the timestamp
        atomicModifyIORef' r $ updateTouchSession mapKey
        return (hi, ho)
  -- run the handler
  h (HandlerInput hi ho)
  where
    updateNewSession :: Int -> (Handle, Handle) -> ProcessHandle -> GlobalState -> (GlobalState, Int)
    updateNewSession mapKey hs ph (GlobalState c m u) =
      (GlobalState (c + 1) (IM.insert mapKey (SessionState c True hs ph) m) u, c)
    updateTouchSession :: Int -> GlobalState -> (GlobalState, Int)
    updateTouchSession = adjustSession touchSession

adjustSession :: (SessionState -> SessionState) -> Int -> GlobalState -> (GlobalState, Int)
adjustSession f mapKey (GlobalState c m u) = (GlobalState c (IM.adjust f mapKey m) u, c)

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
        mimeTypes = HM.map (\m -> append m "; charset=utf-8") defaultMimeTypes,
        indexFiles = ["lecture.html"]
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
      , ("parseCheck",       parseCheckHandler)
      , ("listLectures",     listLecturesHandler)
      , ("loadLecture",      loadLectureHandler)
--      , ("identify/:userid", identifyHandler globRef)
      ] ++ [
        ("/",                serveDirectoryWith myDirConfig "web/")
      ]

togglePrintingAll :: Bool -> HandlerInput -> PeaCoqHandler
togglePrintingAll b input@(HandlerInput hi ho) = do
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
