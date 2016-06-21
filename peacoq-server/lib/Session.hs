module Session where

import Data.IntMap (adjust)

import PeaCoq

isAlive :: SessionState -> Bool
isAlive (SessionState alive _) = alive

markStale :: SessionState -> SessionState
markStale (SessionState _ hs) = SessionState False hs

touchSession :: SessionState -> SessionState
touchSession (SessionState _ hs) = SessionState True hs

adjustSession :: (SessionState -> SessionState) -> Int -> GlobalState ->
                (GlobalState, ())
adjustSession f mapKey gs =
  (gs { gActiveSessions = adjust f mapKey (gActiveSessions gs) }, ())
