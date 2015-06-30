module Coq.Intf.ConstrExpr where

import Coq

import Coq.Intf.DeclKinds
import Coq.Kernel.Names
import Coq.Lib.Loc
import Coq.Library.GlobNames
import Coq.Library.LibNames

type Notation = String

data Explicitation
  = ExplByPos Int (Maybe Id)
  | ExplByName Id

data BinderKind
  = Default BindingKind
  | Generalized BindingKind BindingKind Bool
  deriving (Show)

data AbstractionKind
  = AbsLambda
  | AbsPi
  deriving (Show)

type ProjFlag = Maybe Int

data PrimToken
  = Numeral Integer
  | String String
  deriving (Show)

data RawCasesPatternExpr
  = RCPatAlias Loc RawCasesPatternExpr Id
  | RCPatCstr Loc GlobalReference [RawCasesPatternExpr] [RawCasesPatternExpr]
  | RCPatAtom Loc (Maybe Id)
  | RCPatOr Loc [RawCasesPatternExpr]
  deriving (Show)

data CasesPatternExpr
  = CPatAlias Loc CasesPatternExpr Id
  | CPatCstr Loc Reference [CasesPatternExpr] [CasesPatternExpr]
  | CPatAtom Loc (Maybe Reference)
  | CPatOr Loc [CasesPatternExpr]
  | CPatNotation Loc Notation CasesPatternNotationSubstitution [CasesPatternExpr]
  | CPatPrim Loc PrimToken
  | CPatRecord Loc [(Reference, CasesPatternExpr)]
  | CPatDelimiters Loc String CasesPatternExpr

type CasesPatternNotationSubstitution = ([CasesPatternExpr], [[CasesPatternExpr]])

type InstanceExpr = [GlobLevel]

data ConstrExpr
  = CRef Reference (Maybe InstanceExpr)
  | CFix Loc (Located Id) [FixExpr]
  | CCoFix Loc (Located Id) [CoFixExpr]
  | CProdN Loc [BinderExpr] ConstrExpr
  | CLambdaN Loc [BinderExpr] ConstrExpr
  | CLetIn Loc (Located Name) ConstrExpr ConstrExpr
  | CAppExpl Loc (ProjFlag, Reference, Maybe InstanceExpr) [ConstrExpr]
  | CApp Loc (ProjFlag, ConstrExpr) [(ConstrExpr, Maybe Explicitation)]
  | CRecord Loc (Maybe ConstrExpr) [(Reference, ConstrExpr)]
  | CCases Loc CaseStyle (Maybe ConstrExpr) [CaseExpr] [BranchExpr]
  | CLetTuple Loc [Located Name] (Maybe (Located Name), Maybe ConstrExpr) ConstrExpr ConstrExpr
  | CIf Loc ConstrExpr (Maybe (Located Name), Maybe ConstrExpr) ConstrExpr ConstrExpr
  | CHole Loc (Maybe EvarKinds) IntroPatternNamingExpr (Maybe RawGenericArgument)
  | CPatVar Loc PatVar
  | CEvar Loc ExistentialName [(Id, ConstrExpr)]
  | CSort Loc GlobSort
  | CCast Loc ConstrExpr (CastType ConstrExpr)
  | CNotation Loc Notation ConstrNotationSubstitution
  | CGeneralization Loc BindingKind (Maybe AbstractionKind) ConstrExpr
  | CPrim Loc PrimToken
  | CDelimiters Loc String ConstrExpr
  deriving (Show)

type CaseExpr = (ConstrExpr, (Maybe (Located Name), Maybe CasesPatternExpr))

type BranchExpr = (Loc, [Located [CasesPatternExpr]], ConstrExpr)

type BinderExpr = ([Located Name], BinderKind, ConstrExpr)

type FixExpr = (Located Id, (Maybe (Located Id), RecursionOrderExpr), [LocalBinder], ConstrExpr, ConstrExpr)

type CoFixExpr = (Located Id, [LocalBinder], ConstrExpr, ConstrExpr)

data RecursionOrderExpr
  = CStructRec
  | CWfRec ConstrExpr
  | CMeasureRec ConstrExpr (Maybe ConstrExpr)
  deriving (Show)

data LocalBinder
  = LocalRawDef (Located Name) ConstrExpr
  | LocalRawAssum [Located Name] BinderKind ConstrExpr
  deriving (Show)

type ConstrNotationSubstitution = ([ConstrExpr], [[ConstrExpr]], [[LocalBinder]])

type TypeClassConstraint = (Located Name, BindingKind, ConstrExpr)

type TypeClassContext = [TypeClassConstraint]

type ConstrPatternExpr = ConstrExpr

data WithDeclarationAST
  = CWith_Module (Located [Id]) (Located QualId)
  | CWith_Definition (Located [Id]) ConstrExpr
  deriving (Show)

data ModuleAST
  = CMident (Located QualId)
  | CMapply Loc ModuleAST ModuleAST
  | CMwith Loc ModuleAST WithDeclarationAST
  deriving (Show)
