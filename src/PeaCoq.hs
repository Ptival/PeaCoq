{-# LANGUAGE TemplateHaskell #-}

module PeaCoq where

import Control.Lens         (makeLenses)
import Data.IORef           (IORef)
import Data.IntMap          (IntMap)
import Snap                 (Snaplet)
import Snap.Snaplet.Session (SessionManager)
import System.IO            (Handle)
import System.Process       (ProcessHandle)

import Coq

data SessionState
  = SessionState
    Bool             -- True while the session is alive
    (Handle, Handle) -- I/O handles
    ProcessHandle    -- useful to kill the process
    CoqState         -- the state of the coqtop process

-- Global state must be used in thread-safe way
data GlobalState
  = GlobalState
    Int                   -- next session number
    (IntMap SessionState) -- active sessions

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
