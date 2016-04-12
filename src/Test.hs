module Test where

import Control.Monad.Loops
import Control.Monad.RWS.Strict
import Prelude                  hiding (init)
import System.IO

import Coq.StateId
import Coq.Value
import CoqIO
import Handlers
import XMLProtocol

home :: String
home = "/home/ptival"

coqtop :: String
coqtop = home ++ "/.nix-profile/bin/coqtop -ideslave -main-channel stdfds -I " ++ home ++ "/PeaCoq/plugin -Q " ++ home ++ "/PeaCoq/plugin PeaCoq"

addGoalContext :: String -> CoqtopIO ()
addGoalContext s = do
  add' s
  goal'
  query' "PeaCoqGetContext."
  return (ValueGood ())

main :: IO ()
main = do
  hs <- startCoqtop coqtop
  void $ runRWST (io hs) hs initialCoqState
  where
    io :: Handles -> CoqtopIO ()
    io (_, _, _he, _ph) = do
      init Nothing
      init Nothing
      editAt (StateId 1)
      add' "Require Import PeaCoq.PeaCoq."
      hQuery "Add" "Require Import ZArith."
      hQuery "Goal" ()
      hQuery "Add" "PeaCoqGetContext."
      mapM_ addGoalContext
        [ "Require Import ZArith."
        ]
      -- status False
      -- editAt (StateId 1)
      -- add' "Require Import ZArith."
      --status False
      --editAt (StateId 1)
      --add' "Require Import ZArith."
      -- add' "Require Import PeaCoq.PeaCoq."
      -- add' "Require Import List."
      -- add' "Import ListNotations."
      -- add' "Theorem t : [0] = [1]."
      -- add' "Definition admit {T : Type} : T."
      -- add' "Admitted."
      -- status False
      return (ValueGood ())

{-
      sid <- getStateId
      eid <- newEditID
      r <- hCallRawResponse "Add" (("Import ListNotations.", eid), (sid, False))
      liftIO $ do
        putStrLn $ "Raw response: " ++ r
        --putStrLn $ show (r :: Value AddOutput)
        exit <- waitForProcess ph
        putStrLn $ show exit
      return (ValueGood ())
-}
