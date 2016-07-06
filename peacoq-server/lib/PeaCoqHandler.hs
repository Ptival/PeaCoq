{-# LANGUAGE OverloadedStrings #-}

module PeaCoqHandler where

import           Control.Monad.Except
import           Control.Monad.Loops                 (whileM)
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

import           PeaCoq
import           Session

type PeaCoqHandler a = Handler PeaCoq PeaCoq a

runCommandWithoutBuffering :: String -> IO (Handle, Handle, Handle, ProcessHandle)
runCommandWithoutBuffering cmd = do
  (hi, ho, he, ph) <- runInteractiveCommand cmd
  hSetBuffering hi NoBuffering
  hSetBuffering ho NoBuffering
  hSetBuffering he NoBuffering
  return (hi, ho, he, ph)

getGlobalState :: PeaCoqHandler GlobalState
getGlobalState = do
  globRef <- with lGlobRef ask
  liftIO $ readIORef globRef

modifyGlobalState :: (GlobalState -> (GlobalState, a)) -> PeaCoqHandler a
modifyGlobalState f = do
  globRef <- with lGlobRef ask
  liftIO $ atomicModifyIORef' globRef f

startSertop :: String -> IO Handles
startSertop cmd = do
  liftIO . putStrLn $ "Starting sertop with command: " ++ cmd
  --liftIO $ do
  --  check <- testSertop cmd
  --  case check of
  --    Left err ->
  --      putStrLn $ "\n\n\nSOMETHING LOOKGS WRONG WITH SERTOP: " ++ err ++ "\n\n\n"
  --    Right () -> return ()
  liftIO $ do
    handles@(hi, _, _, _) <- runCommandWithoutBuffering cmd
    hWrite hi "(Control (LibAdd (\"PeaCoq\") \"../PeaCoq/peacoqtop/plugin\" True))"
    hWrite hi "(Control (StmAdd () \"From PeaCoq Require Import PeaCoq.\"))"
    return handles

modifySessionState :: (SessionState -> (SessionState, a)) -> PeaCoqHandler a
modifySessionState f = do
  GlobalState { gActiveSessions = m, gCoqtop = coqtop } <- getGlobalState
  mapKey <- withSession lSession getSessionKey
  case IM.lookup mapKey m of
    Nothing -> do
      hs <- liftIO $ startSertop coqtop
      let (s, res) = f (SessionState True hs)
      modifyGlobalState $ insertSession mapKey s
      --logAction hash $ "NEWSESSION " ++ show sessionIdentity
      return res
    Just s@(SessionState _ (hi, ho, he, ph)) -> do
      exitCode <- liftIO $ getProcessExitCode ph
      case exitCode of
        Just _ -> do
          liftIO $ do
            putStrLn "sertop Quitted, reinitiliazing"
            hClose hi
            hClose ho
            hClose he
          hs <- liftIO $ startSertop coqtop
          let (s', res) = f (SessionState True hs)
          modifyGlobalState . adjustSession (touchSession . const s') $ mapKey
          return res
        Nothing -> do
          -- update the timestamp
          let (s', res) = f s
          modifyGlobalState . adjustSession (touchSession . const s') $ mapKey
          return res

getSessionState :: PeaCoqHandler SessionState
getSessionState = modifySessionState (\ s -> (s, s))

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

withParam :: (FromJSON i, MonadSnap m) => (i -> m o) -> m (Maybe o)
withParam k = do
  let paramName = "data"
  mp <- getParam paramName
  case mp of
    Nothing -> do
      liftIO . putStrLn $
        "Failed to retrieve parameter: " ++ BSU.toString paramName
      return Nothing
    Just bs ->
      -- 'decode' only succeeds on lists and objects, use an artificial list...
      case decodeStrict (BSU.fromString ("[" ++ BSU.toString bs ++ "]")) of
      Just [i] -> Just <$> k i
      _ -> do
        liftIO . putStrLn $
          "Failed to JSON-parse the request parameter: " ++ BSU.toString bs
        return Nothing

hWrite :: Handle -> String -> IO ()
hWrite hi input = do
  putStrLn $ "<- " ++ input
  catchError
    (hPutStrLn hi input)
    (\e -> do
      putStrLn $ "CATCH: Write failed with exception: " ++ show e
    )
  return ()

hRead :: Handle -> IO [String]
hRead ho = do
  -- flush stderr if anything is there... (should report to user?)
  -- putStrLn "Trying to flush he"
  -- whileM_ (hReady he) $ hGetLine he >>= putStrLn

  -- putStrLn "Trying to read ho"
  ls <- whileM (hReady ho) $ do
    -- putStrLn "Trying to read a line:"
    l <- catchError
      (hGetLine ho)
      ((\e -> do
        putStrLn $ "CATCH: Read failed with exception: " ++ show e
        return ""
      ))
    putStrLn $ "-> " ++ l
    return l
  -- putStrLn "Done"

  return ls

handlerCoqtop :: PeaCoqHandler ()
handlerCoqtop = do
  SessionState _ (hi, ho, _, _) <- getSessionState
  void . withParam $ \ input -> do
    res <- liftIO $ do
      hWrite hi input
      -- putStrLn "Waiting for output"
      inputAvailable <- hWaitForInput ho (-1)
      -- putStrLn $ "Wait is over: " ++ show inputAvailable
      if inputAvailable then hRead ho else return []
    writeJSON res

-- no input, but check for output
handlerPing :: PeaCoqHandler ()
handlerPing = do
  SessionState _ (_, ho, _, _) <- getSessionState
  void $ do
    res <- liftIO $ do
      inputAvailable <- hWaitForInput ho 0
      if inputAvailable then hRead ho else return []
    writeJSON res

testSertop :: String -> IO (Either String ())
testSertop sertop = do
  (hi, ho, _, _) <- runCommandWithoutBuffering sertop
  hClose hi
  _ <- hWaitForInput ho 1000
  rdy <- hReady ho
  if rdy
    then do
    eof <- hGetLine ho
    return $ if eof == "(Answer EOF Ack)" || eof == "(Feedback((id(State 1))(contents Processed)(route 0)))"
      then Right ()
      else Left $ "Unexpected answer: " ++ eof
    else do
    return $ Left "Expected output to be ready"
