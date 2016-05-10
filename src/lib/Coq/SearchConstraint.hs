{-# LANGUAGE DeriveGeneric #-}

module Coq.SearchConstraint where

import Data.Aeson            (FromJSON)
import GHC.Generics          (Generic)

import ToXML

data SearchConstraint
  = NamePattern String
  | TypePattern String
  | SubtypePattern String
  | InModule [String]
  | IncludeBlacklist
  deriving (Generic, Show)

instance FromJSON SearchConstraint

tagSearchConstraint :: ToXML a => String -> a -> String
tagSearchConstraint = mkTag "search_cst"

instance ToXML SearchConstraint where
  xml (NamePattern s)    = tagSearchConstraint "name_pattern"      s
  xml (TypePattern s)    = tagSearchConstraint "type_pattern"      s
  xml (SubtypePattern s) = tagSearchConstraint "subtype_pattern"   s
  xml (InModule l)       = tagSearchConstraint "in_module"         l
  xml IncludeBlacklist   = tagSearchConstraint "include_blacklist" ()
