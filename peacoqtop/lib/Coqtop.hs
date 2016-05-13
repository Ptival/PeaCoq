module Coqtop where

import System.IO
import System.Process

startCoqtop :: String -> IO (Handle, Handle, Handle, ProcessHandle)
startCoqtop coqtop = do
  (hi, ho, he, ph) <- runInteractiveCommand coqtop
  hSetBuffering hi NoBuffering
  hSetBuffering ho NoBuffering
  hSetBuffering he NoBuffering
  --hInterp hi "Require Import Unicode.Utf8."
  --hForceValueResponse ho
  return (hi, ho, he, ph)
