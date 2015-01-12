{-# LANGUAGE DeriveFunctor, DeriveGeneric #-}

module CoqTypes where

import Data.Aeson
import Data.Default
import Data.List (intersperse)
import GHC.Generics

import Parser

type Query = String

data Goal
  = MkGoal
    { gId   :: String
    , gHyps :: [Either String Hypothesis]
    , gGoal :: Either String Term
    }
  deriving (Generic)

instance Eq Goal where
  (==) (MkGoal _ hyps1 goal1) (MkGoal _ hyps2 goal2) =
    hyps1 == hyps2 && goal1 == goal2

instance Show Goal where
  show (MkGoal _ hyps goal) =
    concat (intersperse "\n" . map show $ hyps)
    ++ "\n" ++ replicate 40 '=' ++ "\n"
    ++ show goal

instance ToJSON Goal where

data Goals
  = MkGoals
    { focused :: [Goal]
    , unfocused :: [([Goal], [Goal])]
    }
  deriving (Eq, Generic, Show)

instance ToJSON Goals where

data CoqtopResponse r
  = Fail String
  | Good r
  deriving (Eq, Functor, Generic, Show)

instance ToJSON r => ToJSON (CoqtopResponse r) where

instance Default r => Default (CoqtopResponse r) where
  def = Fail def

data PeaCoqResponse
  = MkPeaCoqResponse
    { rGoals :: Goals
    , rResponse :: CoqtopResponse [String]
    }
  deriving (Generic)

instance ToJSON PeaCoqResponse where

data Theorem
  = MkTheorem
    { thModule :: String
    , thName :: String
    , thType :: String
    }
  deriving (Show)
