{-# LANGUAGE OverloadedStrings, RankNTypes #-}

module XMLParsers where

import           Control.Monad.Catch ()
import           Data.Conduit
import           Data.List (intersperse)
import           Data.Maybe (fromMaybe)
import qualified Data.Text as T
import           Data.XML.Types
import           Text.XML.Stream.Parse

import           CoqTypes
import           Parser

type ParseXML a = Consumer Event IO a

parseCoqString :: ParseXML (Maybe String)
parseCoqString = tagNoAttr "string" (T.unpack <$> content)

forceCoqString :: ParseXML String
forceCoqString = force "string" parseCoqString

parseCoqInt :: ParseXML (Maybe String)
parseCoqInt = tagNoAttr "int" (T.unpack <$> content)

forceCoqInt :: ParseXML String
forceCoqInt = force "int" parseCoqInt

parseCoqUnit :: ParseXML (Maybe String)
parseCoqUnit = tagNoAttr "unit" (T.unpack <$> content)

parseOption :: ParseXML (Maybe a) -> ParseXML (Maybe (Maybe a))
parseOption pJust =
  tagName "option" (requireAttr "val") $ \val ->
  case val of
    "some" -> pJust
    "none" -> return Nothing
    _ -> error "option string was neither some nor none"

forceOption :: ParseXML (Maybe a) -> ParseXML (Maybe a)
forceOption pJust = force "option" $ parseOption pJust

parseList :: ParseXML (Maybe a) -> ParseXML (Maybe [a])
parseList p = tagNoAttr "list" $ many p

forceList :: ParseXML (Maybe a) -> ParseXML [a]
forceList p = force "list" $ parseList p

parsePair :: ParseXML a -> ParseXML b -> ParseXML (Maybe (a, b))
parsePair pa pb =
  tagNoAttr "pair" $ do
    a <- pa
    b <- pb
    return (a, b)

forcePair :: ParseXML a -> ParseXML b -> ParseXML (a, b)
forcePair pa pb = force "pair" $ parsePair pa pb

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
      _ -> error "value string was neither fail nor good"

{-
parseSuccessfulCoqtopResponse :: ParseXML t -> ParseXML (Maybe t)
parseSuccessfulCoqtopResponse k =
  tagName "value" (requireAttr "val" <* ignoreAttrs) $ \val ->
    case val of
      "good" -> k
-}

parseValueResponse :: ParseXML (Maybe (CoqtopResponse [String]))
parseValueResponse =
  parseGenericCoqtopResponse
  (many (parseCoqString `orE` parseCoqInt `orE` parseCoqUnit))

forceValueResponse :: ParseXML (CoqtopResponse [String])
forceValueResponse = force "value" parseValueResponse

parseGoal :: ParseXML (Maybe Goal)
parseGoal =
  tagNoAttr "goal" $ do
    goalId <- forceCoqString
    hyps <- (parseHypothesis <$>) <$> forceList parseCoqString
    goal <- parseTerm <$> forceCoqString
    return $ MkGoal goalId hyps goal

forceGoalList :: ParseXML [Goal]
forceGoalList = forceList parseGoal

parseGoals :: ParseXML (Maybe Goals)
parseGoals =
  tagNoAttr "goals" $ do
    foc <- forceList parseGoal
    unfoc <- forceList (parsePair forceGoalList forceGoalList)
    return $ MkGoals foc unfoc

forceGoalResponse :: ParseXML (CoqtopResponse Goals)
forceGoalResponse =
  force "response" $ parseGenericCoqtopResponse $ do
    mgs <- forceOption parseGoals
    return $ fromMaybe (MkGoals [] []) mgs

parseTheorem :: ParseXML (Maybe Theorem)
parseTheorem =
  tagNoAttr "coq_object" $
  do
    modules <- forceList parseCoqString
    name <- forceList parseCoqString
    typ <- forceCoqString
    return $ MkTheorem (concat . intersperse "." $ modules) (name !! 0) typ

parseSearchResponse :: ParseXML (CoqtopResponse [Theorem])
parseSearchResponse =
  force "search" $ parseGenericCoqtopResponse $ forceList parseTheorem

type Status =
  ( [String]      -- a list of sections?
  , Maybe String  -- name of the current definition/theorem
  , [String]      -- list of the current definitions/theorems?
  , String        -- current label (for backtracking)
  , String        -- 1 if in proof, -1 otherwise?
  )

parseStatusResponse :: ParseXML (Maybe Status)
parseStatusResponse =
  tagNoAttr "status" $ do
    l1 <- forceList parseCoqString
    o1 <- forceOption parseCoqString
    l2 <- forceList parseCoqString
    i1 <- forceCoqInt
    i2 <- forceCoqInt
    return (l1, o1, l2, i1, i2)

forceStatusResponse :: ParseXML (CoqtopResponse Status)
forceStatusResponse =
  force "status" $ parseGenericCoqtopResponse $
  force "status" parseStatusResponse
