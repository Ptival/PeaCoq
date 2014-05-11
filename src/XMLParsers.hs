{-# LANGUAGE OverloadedStrings, RankNTypes #-}

module XMLParsers where

import           Control.Applicative ((<$>), (<*))
import           Control.Monad.Catch ()
import           Data.Conduit
import           Data.Maybe (fromMaybe)
import qualified Data.Text as T
import           Data.XML.Types
import           Text.XML.Stream.Parse

import           CoqTypes

type ParseXML a = Consumer Event IO a

parseCoqString :: ParseXML (Maybe String)
parseCoqString = tagNoAttr "string" (T.unpack <$> content)

forceCoqString :: ParseXML String
forceCoqString = force "string" parseCoqString

parseCoqInt :: ParseXML (Maybe String)
parseCoqInt = tagNoAttr "int" (T.unpack <$> content)

parseOption :: ParseXML (Maybe a) -> ParseXML (Maybe (Maybe a))
parseOption pJust =
  tagName "option" (requireAttr "val") $ \val ->
  case val of
    "some" -> pJust
    "none" -> return Nothing

forceOption :: ParseXML (Maybe a) -> ParseXML (Maybe a)
forceOption pJust = force "option" $ parseOption pJust

parseList :: ParseXML (Maybe a) -> ParseXML (Maybe [a])
parseList p = tagNoAttr "list" $ many p

forceList :: ParseXML (Maybe a) -> ParseXML [a]
forceList p = force "list" $ parseList p

parseGenericCoqtopResponse :: ParseXML t -> ParseXML (Maybe (CoqtopResponse t))
parseGenericCoqtopResponse k =
  tagName "value" (requireAttr "val" <* ignoreAttrs) $ \val ->
    case val of
      "fail" -> do
        c <- content
        return . Fail $ T.unpack c
      "good" -> do
        s <- k
        return $ Good s

parseSuccessfulCoqtopResponse :: ParseXML t -> ParseXML (Maybe t)
parseSuccessfulCoqtopResponse k =
  tagName "value" (requireAttr "val" <* ignoreAttrs) $ \val ->
    case val of
      "good" -> k

parseValueResponse :: ParseXML (Maybe (CoqtopResponse [String]))
parseValueResponse =
  parseGenericCoqtopResponse
  (many (parseCoqString `orE` parseCoqInt))

forceValueResponse :: ParseXML (CoqtopResponse [String])
forceValueResponse = force "value" parseValueResponse

parseGoal :: ParseXML (Maybe Goal)
parseGoal =
  tagNoAttr "goal" $ do
    forceCoqString
    hyps <- forceList parseCoqString
    goal <- forceCoqString
    return $ MkGoal hyps goal

parseGoals :: ParseXML (Maybe [Goal])
parseGoals =
  tagNoAttr "goals" $ do
    goals <- forceList parseGoal
    _ <- forceList contentMaybe
    return goals

parseGoalResponse :: ParseXML [Goal]
parseGoalResponse =
  force "response" $ parseSuccessfulCoqtopResponse $ do
    mgs <- forceOption $ parseGoals
    return $ fromMaybe [] mgs
