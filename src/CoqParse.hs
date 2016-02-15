{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module CoqParse where

import Data.Aeson            (ToJSON)
import Data.Proxy
import Data.Tree
import Data.XML.Types
import GHC.Generics          (Generic)
import Text.XML.Stream.Parse hiding (tag)

import FromXML
import Utils

type ParseCoq = Parser (Maybe CoqXMLTree)
type ForceCoq = Parser CoqXMLTree

type ParsePP = Parser (Maybe PPXMLTree)
type ForcePP = Parser PPXMLTree

tagNameLoc :: Name -> AttrParser t ->
             (t -> Parser (CoqXMLTag, Forest LocatedCoqXMLTag)) ->
             ParseCoq
tagNameLoc name otherAttrs recur =
  tagName
  name
  (do b <- castRequireAttr "begin"
      e <- castRequireAttr "end"
      r <- otherAttrs
      return ((b, e), r)
  )
  (\ ((b, e), r) -> do
       (whichNode, contents) <- recur r
       return $ Node (Just (b, e), whichNode) contents
  )

tagNoAttrLoc :: Name -> Parser (CoqXMLTag, Forest LocatedCoqXMLTag) -> ParseCoq
tagNoAttrLoc name recur =
  tagNameLoc name (return ()) $ \ () -> recur

tagNamePos :: Name -> AttrParser t ->
             (t -> Parser (PPXMLTag, Forest (Either String PositionedPPXMLTag))) ->
             ParsePP
tagNamePos name otherAttrs recur =
  tagName
  name
  (do b <- castRequireAttr "startpos"
      e <- castRequireAttr "endpos"
      r <- otherAttrs
      return ((b, e), r)
  )
  (\ ((b, e), r) -> do
       (whichNode, contents) <- recur r
       return $ Node (Right ((b, e), whichNode)) contents
  )

tagNoAttrPos :: Name ->
               Parser (PPXMLTag, Forest (Either String PositionedPPXMLTag)) ->
               ParsePP
tagNoAttrPos name recur =
  tagNamePos name (return ()) $ \ () -> recur

parseOperator :: ParseCoq
parseOperator =
  tagNameLoc "operator"
  (do
       name <- unpackRequireAttr "name"
       kind <- unpackAttr "kind"
       return (name, kind)
  )
  $ \ (name, kind) -> do
    return (Operator name kind, [])

parseConstant :: ParseCoq
parseConstant =
  tagNameLoc "constant" (unpackRequireAttr "name") $ \ name -> do
    return (Constant name, [])

parseToken :: ParseCoq
parseToken =
  tagNoAttrLoc "token" $ do
    c <- unpackContent
    return (Token c, [])

parseTyped :: ParseCoq
parseTyped =
  tagNoAttrLoc "typed" $ do
    r <- many parseConstant
    return (Typed, r)

forceTyped :: ForceCoq
forceTyped = force "Typed" parseTyped

parseRecurse :: ParseCoq
parseRecurse =
  tagNoAttrLoc "recurse" $ do
    r <- many
        $ parseApply
        `orE` parseConstant
        `orE` parseToken
        `orE` parseTyped
    return (Recurse, r)

parseApply :: ParseCoq
parseApply =
  tagNoAttrLoc "apply" $ do
    r <- many $
        parseApply
        `orE` parseConstant
        `orE` parseOperator
        `orE` parseRecurse
        `orE` parseToken
        `orE` parseTyped
    return (Apply, r)

forceApply :: ForceCoq
forceApply = force "Apply" parseApply

parseTheorem :: ParseCoq
parseTheorem =
  tagNameLoc "theorem"
  (do ttype <- unpackRequireAttr "type"
      name  <- unpackRequireAttr "name"
      return (ttype, name))
  $ \ (ttype, name) -> do
    r <- many $
        parseApply
        `orE` parseConstant
    return (Theorem ttype name, r)

forceTheorem :: ForceCoq
forceTheorem = force "Theorem" parseTheorem

parseSectionSubestDescr :: ParseCoq
parseSectionSubestDescr =
  tagName "sectionsubsetdescr" (unpackRequireAttr "name") $ \ name ->
  return $ Node (Nothing, SectionSubsetDescr name) []

parseProof :: ParseCoq
parseProof = tagNoAttrLoc "proof" $ do
  r <- many parseSectionSubestDescr
  return (Proof, r)

forceProof :: ForceCoq
forceProof = force "Proof" parseProof

parseLtac :: ParseCoq
parseLtac = tagNoAttrLoc "ltac" $ do
  c <- unpackContent
  return (Ltac c, [])

parseQED :: ParseCoq
parseQED = tagNoAttrLoc "qed" (return (QED, []))

parseDefinition :: ParseCoq
parseDefinition =
  tagNameLoc "definition"
  (do
       ttype <- unpackRequireAttr "type"
       name  <- unpackRequireAttr "name"
       return (ttype, name)
   )
  $ \ (ttype, name) -> do
    r <- many $
        parseToken
    return (Definition ttype name, r)

parseGallina :: ParseCoq
parseGallina =
  tagNoAttrLoc "gallina" $ do
    r <- many $
        parseDefinition
        `orE` parseProof
        `orE` parseQED
        `orE` parseTheorem
    return (Gallina, r)

forceGallina :: ForceCoq
forceGallina = force "Gallina" parseGallina

parseKeyword :: ParsePP
parseKeyword = tagNoAttrPos "keyword" $ do
  c <- unpackContent
  return (Keyword c, [])

parseVernacExpr :: ParsePP
parseVernacExpr = tagNoAttrPos "vernac_expr" $ do
  r <- many $
      parseKeyword
  c <- unpackContent
  return (VernacExpr c, r)

data CoqXMLTag
  = Apply
  | Constant           String
  | Definition         String String
  | Gallina
  | Ltac               String
  | Operator
    String         -- name
    (Maybe String) -- kind
  | Proof
  | QED
  | Recurse
  | SectionSubsetDescr String
  | Theorem            String String
  | Token              String
  | Typed
  deriving (Generic)

instance ToJSON CoqXMLTag

instance Show CoqXMLTag where
  show Apply                  = "Apply"
  show (Constant s)           = "Constant " ++ s
  show (Definition a b)       = "Definition (" ++ a ++ ") " ++ b
  show Gallina                = "Gallina"
  show (Ltac s)               = "Ltac " ++ s
  show (Operator n mk)        = "Operator " ++ n ++ kind mk
    where
      kind :: Maybe String -> String
      kind Nothing  = ""
      kind (Just k) = " (kind = " ++ k ++ ")"
  show Proof                  = "Proof"
  show QED                    = "QED"
  show (SectionSubsetDescr a) = "SectionSubsetDescr " ++ a
  show Recurse                = "Recurse"
  show (Theorem a b)          = "Theorem (" ++ a ++ ") " ++ b
  show (Token s)              = "Token " ++ s
  show Typed                  = "Typed"

type Location = (Int, Int)

type LocatedCoqXMLTag = (Maybe Location, CoqXMLTag)

instance {-# OVERLAPS #-} Show LocatedCoqXMLTag where
  show (Nothing, t)     = "[?-?] " ++ show t
  show (Just (b, e), t) = "[" ++ show b ++ "-" ++ show e ++ "] " ++ show t

type CoqXMLTree = Tree LocatedCoqXMLTag

instance {-# OVERLAPS #-} Show CoqXMLTree where
  show t = "\n" ++ drawTree (fmap show t)

instance FromXML CoqXMLTree where
  instanceName Proxy = "CoqXMLTree"
  parseXML = parseGallina `orE` parseLtac

data PPXMLTag
  = Keyword String
  | PP String
  | VernacExpr String
  deriving (Generic)

instance Show PPXMLTag where
  show (Keyword s)     = "Keyword " ++ s
  show (PP s)          = "PP" ++ s
  show (VernacExpr s)  = "VernacExpr " ++ s

instance ToJSON PPXMLTag

type Position = (Int, Int)

type PositionedPPXMLTag = (Position, PPXMLTag)

type PPXMLTree = Tree (Either String PositionedPPXMLTag)

instance FromXML PPXMLTree where
  instanceName Proxy = "PPXMLTree"
  parseXML = tagNoAttrPos "pp" $ do
    r <- many $
        parseVernacExpr
    c <- unpackContent
    return (PP c, r)
