
module Session where

import System.IO
import System.Process

data SessionState
  = SessionState
    Int              -- an identifier for the session
    Bool             -- True while the session is alive
    (Handle, Handle) -- I/O handles
    ProcessHandle    -- useful to kill the process

isAlive :: SessionState -> Bool
isAlive (SessionState _ alive _ _) = alive

markStale :: SessionState -> SessionState
markStale (SessionState n _ h ph) = SessionState n False h ph

touchSession :: SessionState -> SessionState
touchSession (SessionState n _ h ph) = SessionState n True h ph

setSession :: Int -> SessionState -> SessionState
setSession ident (SessionState _ t h ph) = SessionState ident t h ph
