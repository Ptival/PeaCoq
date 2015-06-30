module Coq.Kernel.Names where

import Coq.Lib.Canary

type Id = String

data Name
  = Name Id
  | Anonymous
  deriving (Show)

type Variable = Id

type ModuleIdent = Id

type DirPath = [ModuleIdent]

type MBId = (Int, Id, DirPath)

type Label = Id

data ModPath
  = MPFile DirPath
  | MPBound MBId
  | MPDot ModPath Label
  deriving (Show)

type ModulePath = ModPath

data KerName
  = MkKerName
    { canary :: Canary
    , modPath :: ModPath
    , dirPath :: DirPath
    , knLabel :: Label
    , refHash :: Int
    }
  deriving (Show)

type KernelName = KerName

data KerPair
  = Same KerName
  | Dual KerName KerName
  deriving (Show)

type KernelPair = KerPair

type Constant = KerPair

type CPred = () -- TODO

type MutInd = KerPair

type Inductive = (MutInd, Int)
type Constructor = (Inductive, Int)

data EvaluableGlobalReference
  = EvalVarRef Id
  | EvalConstRef Constant
  deriving (Show)

type TransparentState = (IdPred, CPred)

data TableKey a
  = ConstKey a
  | VarKey Id
  | RelKey Int
  deriving (Show)

type InvRelKey = Int

{- Compatibility -}

type Identifier = Id
type IdPred = () -- TODO
--type DirPath = DirPath
type ModBoundId = MBId
--type Label = Id
--type ModulePath = ModPath
--type KernelName = KerName
--type Constant = Constant
type Projection = (Constant, Bool)
type MutualInductive = MutInd
