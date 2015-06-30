module Coq.Lib.Loc where

data Loc =
  MkLoc
  { fName :: String
  , lineNb :: Int
  , bolPos :: Int
  , lineNbLast :: Int
  , bolPosLast :: Int
  , bp :: Int
  , ep :: Int
  }
  deriving (Show)

type Located a = (Loc, a)
