{-# LANGUAGE RankNTypes #-}

module Coqtop where

import           Control.Monad.Catch (MonadThrow)
import qualified Data.ByteString as BS
import           Data.Conduit
import           Data.Conduit.Binary (sourceHandle)
import           Data.Default
import           Data.XML.Types
import           System.IO
import           Text.HTML.TagSoup.Entity (escapeXML)
import           Text.XML.Stream.Parse

import           CoqTypes
import           XMLParsers

xmlConduit :: (MonadThrow m) => Conduit BS.ByteString m Event
xmlConduit = parseBytes $ def { psDecodeEntities = decodeHtmlEntities }

xmlSource :: Handle -> Producer IO Event
xmlSource h = sourceHandle h $= xmlConduit

hCall :: Handle -> [(String, String)] -> String -> IO ()
hCall h args q = do
  let argsStr = concatMap (\(k, v) ->  " " ++ k ++ "=\"" ++ v ++ "\"") args
  let query = "<call id=\"0\"" ++ argsStr ++ ">" ++ escapeXML q ++ "</call>"
  hPutStrLn h query

hInterp :: Handle -> String -> IO ()
hInterp h = hCall h [("val", "interp")]

hGoal :: Handle -> IO ()
hGoal h = hCall h [("val", "goal")] ""

hParseValueResponse :: Handle -> IO (Maybe (CoqtopResponse [String]))
hParseValueResponse h = xmlSource h $$ parseValueResponse

hForceValueResponse :: Handle -> IO (CoqtopResponse [String])
hForceValueResponse h = xmlSource h $$ forceValueResponse

hParseGoalResponse :: Handle -> IO [Goal]
hParseGoalResponse h = xmlSource h $$ parseGoalResponse

hQueryGoal :: Handle -> Handle -> IO [Goal]
hQueryGoal hi ho = do
  hGoal hi
  hParseGoalResponse ho

hQuery :: Handle -> Handle -> Query -> IO (Maybe (Query, [Goal]))
hQuery hi ho q = do
  hInterp hi q
  mr1 <- hParseValueResponse ho
  -- only Show. Undo. if the command succeeded
  case mr1 of
    Just (Good _) -> do
      hGoal hi
      gs <- hParseGoalResponse ho
      hCall hi [("val", "rewind"), ("steps", "1")] ""
      _ <- hParseValueResponse ho
      return $ Just (q, gs)
    Just (Fail _) -> return Nothing

hQueries :: Handle -> Handle -> [Query] -> IO [Maybe (Query, [Goal])]
hQueries hi ho = mapM (hQuery hi ho)

hQueriesUntilFail :: Handle -> Handle -> [Query] -> IO [(Query, [Goal])]
hQueriesUntilFail hi ho l =
  case l of
    [] -> return []
    q : qs -> do
      mqr <- hQuery hi ho q
      case mqr of
        Nothing -> return []
        Just qr -> do
          qrs <- hQueriesUntilFail hi ho qs
          return $ qr : qrs

queries :: [Query]
queries =
  [ "assumption."
  , "auto."
  , "congruence."
  , "destruct 0."
  , "destruct 1."
  , "f_equal."
  , "induction 0."
  , "induction 1."
  , "intro."
  , "match goal with H: _ |- _ => revert H end."
  , "omega."
  , "reflexivity."
  , "simpl."
  , "simpl in *."
  , "transitivity."
  ]

constructors :: [Query]
constructors = map (\i -> "constructor " ++ show i ++ ".") [1 :: Integer ..]
