module Coq.Intf.Locus where

import Coq.Intf.MiscTypes
import Coq.Kernel.Names

data OccurencesGen a
  = AllOccurences
  | AllOccurencesBut [a]
  | NoOccurences
  | OnlyOccurences [a]
  deriving (Show)

type OccurencesExpr = OccurencesGen (OrVar Int)
type WithOccurences a = (OccurencesExpr, a)
type Occurences = OccurencesGen Int

data HypLocationFlag
  = InHyp
  | InHypTypeOnly
  | InHypValueOnly
  deriving (Show)

type HypLocationExpr a = (WithOccurences a, HypLocationFlag)

data ClauseExpr i =
  MkClauseExpr
  { onHyps :: Maybe [HypLocationExpr i]
  , conclOccs :: OccurencesExpr
  }
  deriving (Show)

type Clause = ClauseExpr Id

data ClauseAtom
  = OnHyp Id OccurencesExpr HypLocationFlag
  | OnConcl OccurencesExpr
  deriving (Show)

type ConcreteClause = [ClauseAtom]

type HypLocation = (Id, HypLocationFlag)

type GoalLocation = Maybe HypLocation

type SimpleClause = [Maybe Id]

data OrLikeFirst a
  = AtOccs a
  | LikeFirst
  deriving (Show)
