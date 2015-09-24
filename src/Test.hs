module Test where

import Control.Monad.RWS.Strict
import Prelude                  hiding (init)

import Coq
import Handlers
import XMLProtocol

coqtop :: String
coqtop = "/home/vrobert/coq-build/bin/coqtop -ideslave -main-channel stdfds -I /home/vrobert/PeaCoq/plugin -Q /home/vrobert/PeaCoq/plugin PeaCoq"

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
      add' "Theorem test : True."
      add' "Proof."
      add' "foo."
      add' "bar."
      status False
      add' "idtac."
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
