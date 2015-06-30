module Session where

import Data.IntMap (adjust)

import PeaCoq

isAlive :: SessionState -> Bool
isAlive (SessionState alive _ _ _) = alive

markStale :: SessionState -> SessionState
markStale (SessionState _ h ph st) = SessionState False h ph st

touchSession :: SessionState -> SessionState
touchSession (SessionState _ h ph st) = SessionState True h ph st

adjustSession :: (SessionState -> SessionState) -> Int -> GlobalState ->
                (GlobalState, Int)
adjustSession f mapKey (GlobalState c m) =
  (GlobalState c (adjust f mapKey m), c)
