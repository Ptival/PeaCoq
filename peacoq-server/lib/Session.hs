module Session where

import Data.IntMap (adjust)

import PeaCoq

isAlive :: SessionState -> Bool
isAlive (SessionState alive _ _) = alive

markStale :: SessionState -> SessionState
markStale (SessionState _ hs st) = SessionState False hs st

touchSession :: SessionState -> SessionState
touchSession (SessionState _ hs st) = SessionState True hs st

adjustSession :: (SessionState -> SessionState) -> Int -> GlobalState ->
                (GlobalState, ())
adjustSession f mapKey gs =
  (gs { gActiveSessions = adjust f mapKey (gActiveSessions gs) }, ())

