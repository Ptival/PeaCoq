{-# LANGUAGE DeriveGeneric #-}

module CoqTypes where

import Data.Aeson
import Data.Default
import Data.List (intersperse)
import GHC.Generics

type Query = String

data Goal
  = MkGoal
    { gHyps :: [String]
    , gGoal :: String
    }
  deriving (Eq, Generic)

instance Show Goal where
  show (MkGoal hyps goal) =
    concat (intersperse "\n" hyps)
    ++ "\n" ++ replicate 40 '=' ++ "\n"
    ++ goal

instance ToJSON Goal where

data CoqtopResponse r
  = Fail String
  | Good r
  deriving (Eq, Generic)

instance ToJSON r => ToJSON (CoqtopResponse r) where

instance Default (CoqtopResponse r) where
  def = Fail "DEFAULT"

data RoosterResponse
  = MkRoosterResponse
    { currentGoal :: [Goal]
    , nextGoals :: [(Query, [String])]
    , coqtopResponse :: CoqtopResponse [String]
    }
  deriving (Generic)

instance ToJSON RoosterResponse where
