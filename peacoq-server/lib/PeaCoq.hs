{-# LANGUAGE TemplateHaskell #-}

module PeaCoq where

import Control.Lens         (makeLenses)
import Data.IORef           (IORef)
import Data.IntMap          (IntMap)
import Snap                 (Snaplet)
import Snap.Snaplet.Session (SessionManager)
import System.IO
import System.Process       (ProcessHandle)

type Handles = (Handle, Handle, Handle, ProcessHandle)

data SessionState
  = SessionState
    Bool                     -- True while the session is alive
    Handles                  -- I/O handles

-- Global state must be used in thread-safe way
data GlobalState
  = GlobalState
    { gNextSession :: Int -- number to assign to the next session
    , gActiveSessions :: IntMap SessionState
    , gCoqtop :: String -- the command to use to run coqtop
    }

type PeaCoqGlobRef = (IORef GlobalState)
type PeaCoqHash    = String
type PeaCoqSession = SessionManager

-- Each thread gets a separate copy of this, fields must be read-only
data PeaCoq
  = PeaCoq
    { _lGlobRef :: Snaplet PeaCoqGlobRef
    , _lHash    :: Snaplet PeaCoqHash
    , _lSession :: Snaplet PeaCoqSession
    }

-- Fields are lenses to separate concerns, use "Handler PeaCoq <Lens> a"
makeLenses ''PeaCoq
