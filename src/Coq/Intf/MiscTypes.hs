module Coq.Intf.MiscTypes where

import Coq.Kernel.Evar
import Coq.Kernel.Names
import Coq.Lib.Loc

type PatVar = Id

data IntroPatternExpr c
  = IntroForthcoming Bool
  | IntroNaming IntroPatternNamingExpr
  | IntroAction (IntroPatternActionExpr c)
  deriving (Show)

data IntroPatternNamingExpr
  = IntroIdentifier Id
  | IntroFresh Id
  | IntroAnonymous
  deriving (Show)

data IntroPatternActionExpr c
  = IntroWildcard
  | IntroOrAndPattern (OrAndIntroPatternExpr c)
  | IntroInjection [(Loc, IntroPatternExpr c)]
  | IntroApplyOn c (Loc, IntroPatternExpr c)
  | IntroRewrite Bool
  deriving (Show)

type OrAndIntroPatternExpr c = [[(Loc, IntroPatternExpr c)]]

data MoveLocation i
  = MoveAfter i
  | MoveBefore i
  | MoveFirst
  | MoveLast
  deriving (Show)

data GlobSortGen a
  = GProp
  | GSet
  | GType a
  deriving (Show)

type SortInfo = [String]
type LevelInfo = Maybe String
type GlobSort = GlobSortGen SortInfo
type GlobLevel = GlobSortGen LevelInfo

type ExistentialKey = Evar

data CastType a
  = CastConv a
  | CastVM a
  | CastCoerce
  | CastNative a
  deriving (Show)

data QuantifiedHypothesis
  = AnonHyp Int
  | NamedHyp Id
  deriving (Show)

type ExplicitBindings a = [(Loc, QuantifiedHypothesis, a)]

data Bindings a
  = ImplicitBindings [a]
  | ExplicitBindings (ExplicitBindings a)
  | NoBindings
  deriving (Show)

type WithBindings a = (a, Bindings a)

data OrVar a
  = ArgArg a
  | ArgVar (Located Id)
  deriving (Show)

type AndShortName a = (a, Maybe (Located Id))

data OrByNotation a
  = AN a
  | ByNotation Loc String (Maybe String)
  deriving (Show)

data ModuleKind
  = Module
  | ModType
  | ModAny
  deriving (Show)
