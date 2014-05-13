{-# LANGUAGE OverloadedStrings, RankNTypes #-}

module Main where

import Control.Applicative ((<$>), (<|>))
import Control.Monad.IO.Class (liftIO)
import Data.ByteString.UTF8
import Data.List (nubBy)
import Data.Maybe (catMaybes)
import Snap.Core
import Snap.Extras.JSON
import Snap.Http.Server (quickHttpServe)
import Snap.Util.FileServe (serveFile, serveDirectory)
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
  return (hi, ho)

main :: IO ()
main = do
  (hi, ho) <- startCoqtop
  quickHttpServe (site hi ho)

site :: Handle -> Handle -> Snap ()
site hi ho =
  ifTop (serveFile "web/rooster.html")
  <|> route [ ("query", queryHandler hi ho) ]
  <|> serveDirectory "web/"
  <|> serveDirectory "web/jquery-ui-1.10.4.custom/css/south-street/"

pprintResponse :: CoqtopResponse [String] -> String
pprintResponse (Fail s) = s
pprintResponse (Good l) = concatMap (++ "\n") l

queryHandler :: Handle -> Handle -> Snap ()
queryHandler hi ho = do
  param <- getParam "query"
  case param of
    Nothing -> return ()
    Just queryBS -> do
      response <- liftIO $ do
        -- might want to sanitize? :3
        --let query = BSC.unpack queryBS
        let query = toString queryBS
        putStrLn $ "LOG: " ++ query
        hInterp hi query
        response <- hForceValueResponse ho

        goals <- hQueryGoal hi ho

        -- maybe not do that every time? :)
        hCall hi [("val", "search")] ""
        rthms <- hParseSearchResponse ho

        let thms = case rthms of
              Good ts -> ts
              Fail _  -> []

        let hyps = gCurHypsNames goals

        let destructs = map (\h -> "destruct " ++ h ++ ".") hyps
        let inductions = map (\h -> "induction " ++ h ++ ".") hyps
        let l2r = map (\h -> "rewrite -> " ++ h ++ ".") hyps
        let r2l = map (\h -> "rewrite <- " ++ h ++ ".") hyps
        let applies = map (\t -> "apply " ++ thName t ++ ".") thms

        simpleQueries <- catMaybes <$> hQueries hi ho queries
        destructQueries <- catMaybes <$> hQueries hi ho destructs
        inductionQueries <- catMaybes <$> hQueries hi ho inductions
        constructorQueries <- hQueriesUntilFail hi ho constructors
        l2rQueries <- catMaybes <$> hQueries hi ho l2r
        r2lQueries <- catMaybes <$> hQueries hi ho r2l
        applyQueries <- catMaybes <$> hQueries hi ho applies

        let queryResults =
              nubBy (\q1 q2 -> snd q1 == snd q2)
              . filter (\qr -> snd qr /= goals)
              $ simpleQueries
              ++ destructQueries
              ++ inductionQueries
              ++ constructorQueries
              ++ l2rQueries
              ++ r2lQueries
              ++ applyQueries

        let nexts = map (\(x, y) -> (x, y))
                    $ queryResults

        return $ MkRoosterResponse goals nexts response
      writeJSON response
