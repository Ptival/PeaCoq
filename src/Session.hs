module Session where

import PeaCoq

isAlive :: SessionState -> Bool
isAlive (SessionState _ alive _ _) = alive

markStale :: SessionState -> SessionState
markStale (SessionState n _ h ph) = SessionState n False h ph

touchSession :: SessionState -> SessionState
touchSession (SessionState n _ h ph) = SessionState n True h ph

setSession :: Int -> SessionState -> SessionState
setSession ident (SessionState _ t h ph) = SessionState ident t h ph
