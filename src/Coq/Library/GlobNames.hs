module Coq.Library.GlobNames where

import Coq.Kernel.Names

data GlobalReference
  = VarRef Variable
  | ConstRef Constant
  | ConstructRef Constructor
  | IndRef Inductive
  deriving (Show)

type SynDefName = KernelName

data ExtendedGlobalReference
  = TrueGlobal GlobalReference
  | SynDef SynDefName
  deriving (Show)

data GlobalReferenceOrConstr
  = IsGlobal GlobalReference
  | IsConstr Constr
  deriving (Show)
