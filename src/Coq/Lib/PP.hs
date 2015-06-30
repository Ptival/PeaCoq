module Coq.Lib.PP where

import OCaml

data Glue a
  = GEmpty
  | GLeaf a
  | GNode (Glue a) (Glue a)
  deriving (Show)

type Tag = (Int, Obj)

type TagKey = Int

data BlockType
  = PPHBox Int
  | PPVBox Int
  | PPHVBox Int
  | PPHOVBox Int
  | PPTBox
  deriving (Show)

data StrToken
  = StrDef String
  | StrLen String Int
  deriving (Show)

data PPCmdToken a
  = PPCmdPrint a
  | PPCmdBox BlockType (Glue (PPCmdToken a))
  | PPCmdPrintBreak Int Int
  | PPCmdSetTab
  | PPCmdPrintTBreak Int Int
  | PPCmdWhiteSpace Int
  | PPCmdForceNewline
  | PPCmdPrintIfBroken
  | PPCmdOpenBox BlockType
  | PPCmdCloseBox
  | PPCmdCloseTBox
  | PPCmdComment Int
  | PPCmdOpenTag Tag
  | PPCmdCloseTag
  deriving (Show)

data PPDirToken a
  = PPDirPPCmds (Glue (PPCmdToken a))
  | PPDirPrintNewline
  | PPDirPrintFlush
  deriving (Show)

type PPCmd = PPCmdToken StrToken

type StdPPCmds = Glue PPCmd

type PPDirs a = Glue (PPDirToken a)

type TagHandler = Tag -> FormatTag
