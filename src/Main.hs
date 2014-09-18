{-# LANGUAGE OverloadedStrings, RankNTypes #-}

module Main where

import Control.Applicative ((<$>), (<|>))
import Control.Monad.IO.Class (liftIO)
import Data.ByteString (append)
import Data.ByteString.UTF8 (toString)
import Data.List (nubBy, (\\))
import qualified Data.HashMap.Strict as HM (map)
import Data.Maybe (catMaybes)
import Snap.Core
import Snap.Extras.JSON
import Snap.Http.Server (quickHttpServe)
import Snap.Util.FileServe
import System.IO
import System.Process (runInteractiveCommand)

import CoqTypes
import Coqtop

startCoqtop :: IO (Handle, Handle)
startCoqtop = do
  (hi, ho, _, _) <- runInteractiveCommand "coqtop -ideslave"
  hSetBinaryMode hi False
  hSetBuffering stdin LineBuffering
  hSetBuffering hi NoBuffering
  hInterp hi "Require Import Unicode.Utf8."
  hForceValueResponse ho
  return (hi, ho)

main :: IO ()
main = do
  (hi, ho) <- startCoqtop
  quickHttpServe (site hi ho)

myDirConfig = defaultDirectoryConfig {
  mimeTypes = HM.map (\m -> append m "; charset=utf-8") defaultMimeTypes
  }

site :: Handle -> Handle -> Snap ()
site hi ho =
  ifTop (serveFile "web/rooster.html")
  <|> route [ ("query", queryHandler hi ho) ]
  <|> route [ ("undo", undoHandler hi ho) ]
  <|> route [ ("queryundo", queryUndoHandler hi ho) ]
  <|> route [ ("status", statusHandler hi ho) ]
  <|> route [ ("rewind", rewindHandler hi ho) ]
  <|> route [ ("qed", qedHandler hi ho) ]
  <|> route [ ("setprintingall", togglePrintingAll True hi ho) ]
  <|> route [ ("unsetprintingall", togglePrintingAll False hi ho) ]
  <|> serveDirectoryWith myDirConfig "web/"
  <|> serveDirectory "web/jquery-ui-1.10.4.custom/css/south-street/"

pprintResponse :: CoqtopResponse [String] -> String
pprintResponse (Fail s) = s
pprintResponse (Good l) = concatMap (++ "\n") l

goalsOfGoals :: Goals -> [Goal]
goalsOfGoals (MkGoals foc unfoc) = foc ++ concatMap (uncurry (++)) unfoc

newGoals :: Goals -> Goals -> [Goal]
newGoals old new = goalsOfGoals new \\ goalsOfGoals old

proofContextWithNext :: Handle -> Handle -> IO (Goals, [(Query, [Goal])])
proofContextWithNext hi ho = do
  goals <- hQueryGoal hi ho

{-
  -- maybe not do that every time? :)
  hCall hi [("val", "search")] ""
  rthms <- hParseSearchResponse ho

  let thms = case rthms of
        Good ts -> ts
        Fail _  -> []
-}

  let hyps = gCurHypsNames goals

  let destructs = map (\h -> "destruct " ++ h ++ ".") hyps
  let inductions = map (\h -> "induction " ++ h ++ ".") hyps
  let l2r = map (\h -> "rewrite -> " ++ h ++ ".") hyps
  let r2l = map (\h -> "rewrite <- " ++ h ++ ".") hyps
  -- let applies = map (\t -> "apply " ++ thName t ++ ".") thms
  let applyhyps = map (\h -> "apply " ++ h ++ ".") hyps
  let reverts = map (\h -> "revert " ++ h ++ ".") hyps

  simpleQueries <- catMaybes <$> hQueries hi ho queries
  destructQueries <- catMaybes <$> hQueries hi ho destructs
  inductionQueries <- catMaybes <$> hQueries hi ho inductions
  constructorQueries <- hQueriesUntilFail hi ho constructors
  l2rQueries <- catMaybes <$> hQueries hi ho l2r
  r2lQueries <- catMaybes <$> hQueries hi ho r2l
  -- applyQueries <- catMaybes <$> hQueries hi ho applies
  applyHypsQueries <- catMaybes <$> hQueries hi ho applyhyps
  revertQueries <- catMaybes <$> hQueries hi ho reverts

  let queryResults =
        -- remove duplicates when multiple queries have equivalent effect
        nubBy (\q1 q2 -> snd q1 == snd q2)
        -- remove queries that don't affect the state
        . filter (\qr -> snd qr /= goals)
        $ simpleQueries
        ++ destructQueries
        ++ inductionQueries
        ++ constructorQueries
        ++ l2rQueries
        ++ r2lQueries
        -- ++ applyQueries
        ++ applyHypsQueries
        ++ revertQueries

  let queryResults' =
        map (\(q, goals') -> (q, newGoals goals goals')) queryResults

  return (goals, queryResults')

queryHandler :: Handle -> Handle -> Snap ()
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
      respond hi ho response

respond :: Handle -> Handle -> CoqtopResponse [String] -> Snap ()
respond hi ho response = do
  goals <- liftIO $ hQueryGoal hi ho
  writeJSON $ MkRoosterResponse goals response

undoHandler :: Handle -> Handle -> Snap ()
undoHandler hi ho = do
  liftIO $ hCall hi [("val", "rewind"), ("steps", "1")] ""
  r <- liftIO $ hForceValueResponse ho
  respond hi ho r

statusHandler :: Handle -> Handle -> Snap ()
statusHandler hi ho = do
  liftIO $ hCall hi [("val", "status")] ""
  r <- liftIO $ hForceStatusResponse ho
  respond hi ho (return . show <$> r)

rewindHandler :: Handle -> Handle -> Snap ()
rewindHandler hi ho = do
  param <- getParam "query"
  case param of
    Nothing -> return ()
    Just stepsBS -> do
      liftIO $ hCall hi [("val", "rewind"), ("steps", toString stepsBS)] ""
      r <- liftIO $ hForceValueResponse ho
      respond hi ho (return . show <$> r)

qedHandler :: Handle -> Handle -> Snap ()
qedHandler hi ho = do
  liftIO $ hInterp hi "Qed."
  r <- liftIO $ hForceValueResponse ho
  respond hi ho r

queryUndoHandler :: Handle -> Handle -> Snap ()
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
      respond hi ho response
      case response of
        Fail _ ->
          return ()
        Good _ ->
          do
            liftIO $ hCall hi [("val", "rewind"), ("steps", "1")] ""
            liftIO $ hForceValueResponse ho
            return ()

setPrintingAll :: Handle -> Handle -> Snap ()
setPrintingAll hi ho = do
  let query =
        "<call id=\"0\" val=\"setoptions\">"
        ++ "<pair><list><string>Printing</string><string>All</string></list>"
        ++ "<option_value val=\"boolvalue\"><bool val=\"true\"></bool></option_value>"
        ++ "</pair></call>"
  liftIO $ hPutStrLn hi query
  r <- liftIO $ hForceValueResponse ho
  respond hi ho r

togglePrintingAll :: Bool -> Handle -> Handle -> Snap ()
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
  respond hi ho r
