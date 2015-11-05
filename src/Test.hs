module Test where

import Control.Monad.RWS.Strict
import Prelude                  hiding (init)

import Coq
import Handlers
import XMLProtocol

coqtop :: String
coqtop = "/home/ptival/.nix-profile/bin/coqtop -ideslave -main-channel stdfds -I /home/vrobert/PeaCoq/plugin -Q /home/vrobert/PeaCoq/plugin PeaCoq"

main :: IO ()
main = do
  hs <- startCoqtop coqtop
  void $ runRWST (io hs) hs initialCoqState
  where
    io :: Handles -> CoqtopIO ()
    io (_, _, _he, _ph) = do
      init Nothing
      --add' "Require Import PeaCoq.PeaCoq."
      --add' "Require Import List."
      --add' "Import ListNotations."
      --add' "Theorem t : [0] = [1]."
      add' "Definition admit {T : Type} : T."
      add' "Admitted."
      status False
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
