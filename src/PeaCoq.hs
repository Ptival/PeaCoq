{-# LANGUAGE TemplateHaskell #-}

module PeaCoq where

import           Control.Lens
import           Snap
import           Snap.Snaplet.Session (SessionManager)

data PeaCoq
  = PeaCoq
    { _lSession :: Snaplet SessionManager
    }

makeLenses ''PeaCoq
