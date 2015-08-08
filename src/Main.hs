{-# LANGUAGE OverloadedStrings #-}

module Main where

import           Control.Concurrent                          (forkIO, threadDelay)
import           Control.Monad                               (forever, forM)
import           Control.Monad.IO.Class                      (liftIO)
import           Data.ByteString                             (ByteString, append)
import qualified Data.HashMap.Strict                         as HM (map)
import           Data.IORef
import qualified Data.IntMap                                 as IM
import           Data.Time.Format
import           Data.Time.LocalTime
import           Network.Socket
import           Prelude                                     hiding (log)
import           Snap.Core                                   (MonadSnap)
import           Snap.Http.Server.Config
import           Snap.Snaplet
import           Snap.Snaplet.Session                        hiding (touchSession)
import           Snap.Snaplet.Session.Backends.CookieSession (initCookieSessionManager)
import           Snap.Snaplet.Session.SessionManager         ()
import           Snap.Util.FileServe
import           System.IO
import           System.Log.Formatter
import           System.Log.Handler                          (setFormatter)
import           System.Log.Handler.Simple
import           System.Log.Logger
import           System.Process

import           Config
import           Handlers
import           PeaCoq
import           Session

{- Configuration -}

sessionTimeoutMinutes :: Int
sessionTimeoutMinutes = 15

peacoqRoutes :: [(ByteString, PeaCoqHandler ())]
peacoqRoutes =
  -- Coqtop routes
  [ ("about",      handlerAbout)
  , ("add",        handlerAdd)
  , ("annotate",   handlerAnnotate)
  , ("editat",     handlerEditAt)
  , ("evars",      handlerEvars)
  , ("getoptions", handlerGetOptions)
  , ("goal",       handlerGoal)
  , ("hints",      handlerHints)
  --, ("init",       handlerInit)
  , ("interp",     handlerInterp)
  , ("mkcases",    handlerMkCases)
  , ("printast",   handlerPrintAST)
  , ("query",      handlerQuery)
  , ("quit",       handlerQuit)
  , ("search",     handlerSearch)
  , ("setoptions", handlerSetOptions)
  , ("status",     handlerStatus)
  , ("stopworker", handlerStopWorker)
  ] ++
  -- Coqtop additional routes
  [ ("add'",       handlerAdd')
  , ("query'",     handlerQuery')
  ] ++
  -- PeaCoq-specific routes
  [ ("/", serveDirectoryWith myDirConfig "web/")
  ]

{- End of configuration -}

data PeaCoqConfig =
  PeaCoqConfig
  { configUserId  :: Maybe String
  , configLogPath :: FilePath
  }
  deriving (Read)

serverConfig :: MonadSnap m => String -> Config m a
serverConfig nowString =
  setStartupHook hook -- figures out which port was used and prints it
  . setPort 0         -- 0 means that unless specified, pick a random port
  . setAccessLog (ConfigFileLog $ prefix ++ "access.log")
  . setErrorLog (ConfigFileLog $ prefix ++ "error.log")
  $ defaultConfig
  where
    prefix = logPath ++ "/" ++ userId ++ "-" ++ nowString ++ "-"
    hook dat = do
      port <- socketPort . head $ getStartupSockets dat
      putStrLn $ "Server listening on port: " ++ show port
      --putStrLn $ "On recycle, visit: http://recycle.cs.washington.edu:" ++ show port
      --putStrLn $ "On attu, visit: http://attu.cs.washington.edu:" ++ show port
      --putStrLn $ "Otherwise, visit: http://localhost:" ++ show port

main :: IO ()
main = do
  now <- getZonedTime
  let nowString = formatTime defaultTimeLocale "%F-%H-%M-%S" now
  handler <- fileHandler
            (logPath ++ "/" ++ userId ++ "-" ++ nowString ++ ".log")
            loggingPriority
  let format = simpleLogFormatter "[$time] $msg"
  let fHandler = setFormatter handler format
  updateGlobalLogger rootLoggerName (setLevel loggingPriority . addHandler fHandler)
  serveSnaplet (serverConfig nowString) peaCoqSnaplet

sessionTimeoutSeconds :: Int
sessionTimeoutSeconds = 60 * sessionTimeoutMinutes

sessionTimeoutMicroseconds :: Int
sessionTimeoutMicroseconds = sessionTimeoutSeconds * 1000 * 1000

loggingPriority :: Priority
loggingPriority = INFO

closeSession :: String -> SessionState -> IO ()
closeSession _hash (SessionState _ (hi, ho) ph _) = do
  --logAction hash $ "END SESSION " ++ show sessId
  hClose hi
  hClose ho
  terminateProcess ph -- not stricly necessary
  waitForProcess ph
  return ()

cleanStaleSessions :: String -> IORef GlobalState -> IO ()
cleanStaleSessions hash globRef = forever $ do
  GlobalState _ _ <- readIORef globRef
  sessionsToClose <- atomicModifyIORef' globRef markAndSweep
  forM sessionsToClose (closeSession hash)
  threadDelay sessionTimeoutMicroseconds
  where
    markAndSweep :: GlobalState -> (GlobalState, [SessionState])
    markAndSweep (GlobalState c m) =
      let (alive, stale) = IM.partition isAlive m in
      (GlobalState c (IM.map markStale alive), IM.elems stale)

newPeaCoqGlobalState :: String -> IO (IORef GlobalState)
newPeaCoqGlobalState hash = liftIO $ do
  globRef <- newIORef $ GlobalState 0 IM.empty
  -- spawn a parallel thread to regularly clean up
  forkIO $ cleanStaleSessions hash globRef
  return globRef

globRefInit :: IORef GlobalState -> SnapletInit PeaCoq PeaCoqGlobRef
globRefInit globRef =
  makeSnaplet "globRef" "Holds PeaCoq's global state IORef" Nothing $ do
    return globRef

hashInit :: String -> SnapletInit PeaCoq PeaCoqHash
hashInit hash =
  makeSnaplet "hash" "Holds the current git commit hash" Nothing $ do
    return hash

peaCoqSnaplet :: SnapletInit PeaCoq PeaCoq
peaCoqSnaplet = makeSnaplet "PeaCoq" "PeaCoq" Nothing $ do
  hash <- liftIO $ getGitCommitHash
  globRef <- liftIO $ newPeaCoqGlobalState hash
  g <- nestSnaplet "globRef" lGlobRef $ globRefInit globRef
  h <- nestSnaplet "hash" lHash $ hashInit hash
  s <- nestSnaplet "session" lSession cookieSessionManager
  addRoutes peacoqRoutes
  return $ PeaCoq g h s
  where
    cookieSessionManager :: SnapletInit PeaCoq SessionManager
    cookieSessionManager =
      initCookieSessionManager "encryption_key" "peacoq_session" Nothing

myDirConfig :: DirectoryConfig (Handler PeaCoq PeaCoq)
myDirConfig =
  defaultDirectoryConfig
  { mimeTypes = HM.map (\ m -> append m "; charset=utf-8") defaultMimeTypes
  , indexFiles = ["lecture.html"]
  }
