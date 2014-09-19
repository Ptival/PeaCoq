{-# LANGUAGE TemplateHaskell #-}

module Rooster where

import           Control.Lens
import           Snap
import           Snap.Snaplet.Session (SessionManager)

data Rooster
  = Rooster
    { _lSession :: Snaplet SessionManager
    }

makeLenses ''Rooster
