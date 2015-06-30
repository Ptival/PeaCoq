module Coq.Library.LibNames where

import Coq.Kernel.Names
import Coq.Lib.Loc

type FullPath = (DirPath, Id)

type QualId = FullPath

type ObjectName = (FullPath, KernelName)

type ObjectPrefix = (DirPath, (ModulePath, DirPath))

data GlobalDirReference
  = DirOpenModule ObjectPrefix
  | DirOpenModtype ObjectPrefix
  | DirOpenSection ObjectPrefix
  | DirModule ObjectPrefix
  | DirClosedSection DirPath
  deriving (Show)

data Reference
  = QualId (Located QualId)
  | Ident (Located Id)
  deriving (Show)
