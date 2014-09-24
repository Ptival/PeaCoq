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
import           System.Process
import           System.Random

import           CoqTypes
import           Coqtop
import           Parser
import           Rooster

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

type RoosterHandler = Handler Rooster Rooster ()

type HandledRoosterHandler = Handle -> Handle -> RoosterHandler

sessionTimeoutSeconds :: Int
sessionTimeoutSeconds = 3600

sessionTimeoutMicroseconds :: Int
sessionTimeoutMicroseconds = sessionTimeoutSeconds * 1000 * 1000

main :: IO ()
main = do
  globRef <- newIORef $ GlobalState 0 IM.empty
  forkIO $ cleanStaleSessions globRef
  serveSnaplet defaultConfig $ roosterSnaplet globRef

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
  forM sessionsToClose $ \(SessionState n _ (hi, ho) ph) -> do
    log $ "Terminating coqtop session " ++ show n
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
  -> HandledRoosterHandler
  -> RoosterHandler
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
  (hi, ho) <- liftIO $ do
    GlobalState _ m <- readIORef r
    case IM.lookup mapKey m of
      Nothing -> do
        (hi, ho, ph) <- startCoqtop
        n <- atomicModifyIORef' r $ updateNewSession mapKey (hi, ho) ph
        log $ "Starting coqtop session " ++ show n
        return (hi, ho)
      Just (SessionState _ _ hiho _) -> do
        -- update the timestamp
        atomicModifyIORef' r $ updateTouchSession mapKey
        return hiho
  -- run the handler
  h hi ho
  where
    updateNewSession
      :: Int -> (Handle, Handle) -> ProcessHandle -> GlobalState -> (GlobalState, Int)
    updateNewSession mapKey hs ph (GlobalState c m) =
      (GlobalState (c + 1) (IM.insert mapKey (SessionState c True hs ph) m), c)
    updateTouchSession :: Int -> GlobalState -> (GlobalState, Int)
    updateTouchSession mapKey (GlobalState c m) =
      (GlobalState c (IM.adjust touchSession mapKey m), c)

roosterSnaplet :: IORef GlobalState -> SnapletInit Rooster Rooster
roosterSnaplet globRef = makeSnaplet "Rooster" "Rooster" Nothing $ do
  s <- nestSnaplet "session" lSession cookieSessionManager
  addRoutes roosterRoutes
  return $ Rooster s
  where
    cookieSessionManager :: SnapletInit Rooster SessionManager
    cookieSessionManager = initCookieSessionManager "encryption_key" "rooster_session" Nothing
    myDirConfig :: DirectoryConfig (Handler Rooster Rooster)
    myDirConfig =
      defaultDirectoryConfig {
        mimeTypes = HM.map (\m -> append m "; charset=utf-8") defaultMimeTypes
        }
    roosterRoutes :: [(ByteString, RoosterHandler)]
    roosterRoutes =
      map (\(r, handler) -> (r, withSessionHandles globRef handler))
      [ ("query",            queryHandler)
      , ("queryundo",        queryUndoHandler)
      , ("undo",             undoHandler)
      , ("status",           statusHandler)
      , ("rewind",           rewindHandler)
      , ("qed",              qedHandler)
      , ("setprintingall",   togglePrintingAll True)
      , ("unsetprintingall", togglePrintingAll False)
      , ("parse",            parseHandler)
      ] ++
      [ ("/",                serveDirectoryWith myDirConfig "web/")
      ]

respond :: CoqtopResponse [String] -> HandledRoosterHandler
respond response hi ho = do
  goals <- liftIO $ hQueryGoal hi ho
  writeJSON $ MkRoosterResponse goals response

parseHandler :: HandledRoosterHandler
parseHandler _ _ = do
  param <- getParam "query"
  case param of
    Nothing -> return ()
    Just queryBS -> do
      let response = parseVernac $ toString queryBS
      writeJSON response

queryHandler :: HandledRoosterHandler
queryHandler hi ho = do
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
      respond response hi ho

queryUndoHandler :: HandledRoosterHandler
queryUndoHandler hi ho = do
  param <- getParam "query"
  case param of
    Nothing -> return ()
    Just queryBS -> do
      response <- liftIO $ do
        -- might want to sanitize? :3
        let query = toString queryBS
        hInterp hi query
        hForceValueResponse ho
      respond response hi ho
      case response of
        Fail _ ->
          return ()
        Good _ ->
          do
            liftIO $ hCall hi [("val", "rewind"), ("steps", "1")] ""
            liftIO $ hForceValueResponse ho
            return ()

undoHandler :: HandledRoosterHandler
undoHandler hi ho = do
  liftIO $ hCall hi [("val", "rewind"), ("steps", "1")] ""
  r <- liftIO $ hForceValueResponse ho
  respond r hi ho

statusHandler :: HandledRoosterHandler
statusHandler hi ho = do
  liftIO $ hCall hi [("val", "status")] ""
  r <- liftIO $ hForceStatusResponse ho
  respond (return . show <$> r) hi ho

rewindHandler :: HandledRoosterHandler
rewindHandler hi ho = do
  param <- getParam "query"
  case param of
    Nothing -> return ()
    Just stepsBS -> do
      liftIO $ hCall hi [("val", "rewind"), ("steps", toString stepsBS)] ""
      r <- liftIO $ hForceValueResponse ho
      respond (return . show <$> r) hi ho

qedHandler :: HandledRoosterHandler
qedHandler hi ho = do
  liftIO $ hInterp hi "Qed."
  r <- liftIO $ hForceValueResponse ho
  respond r hi ho

togglePrintingAll :: Bool -> HandledRoosterHandler
togglePrintingAll b hi ho = do
  let query =
        "<call id=\"0\" val=\"setoptions\">"
        ++ "<pair><list><string>Printing</string><string>All</string></list>"
        ++ "<option_value val=\"boolvalue\"><bool val=\""
        ++ (if b then "true" else "false")
        ++ "\"></bool></option_value>"
        ++ "</pair></call>"
  liftIO $ hPutStrLn hi query
  r <- liftIO $ hForceValueResponse ho
  respond r hi ho
