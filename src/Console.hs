module Console where

import Control.Exception
import Control.Monad.RWS.Strict
--import Data.Tree
import Prelude                  hiding (init)
import Text.XML.Stream.Parse
import System.IO
import System.Process

import Config
import Coq
import ShowXML
import XMLProtocol

startCoqtop :: IO (Handle, Handle, ProcessHandle)
startCoqtop = do
  (hi, ho, he, ph) <- runInteractiveCommand coqtop
  hClose he
  hSetBinaryMode hi False
  hSetBuffering stdin LineBuffering
  hSetBuffering hi NoBuffering
  return (hi, ho, ph)

handleExceptions :: IO () -> IO ()
handleExceptions = handle $ \ e -> do
  --print (e :: XmlException)
  putStrLn "\n\n\nXML parsing failed with an exception"
  putStrLn $ xmlErrorMessage e
  putStrLn "Bad input:"
  putStrLn . showXML $ xmlBadInput e
  return ()

main :: IO ()
main = do
  (hi, ho, _) <- startCoqtop
  handleExceptions . void . runCoqtopIO (hi, ho) initialCoqState $ do
    init Nothing
    add' "Definition t := 0."
    --add' "Lemma l : true && true <> false."
    --s <- getStateId
    --printAST s

    {-
    evars'
    init Nothing
    about'
    add' "Lemma a : (42 : nat) = 42."
    s <- getStateId
    add' "Proof."
    annotate "Print bool."
    goal'
    editAt s
    getOptions'
    hints'
    interp ((False, False), "Print bool.")
    mkCases "nat"
    printAST s
    query' "Print bool."
    search [(NamePattern "nat_ind", True)]
    setOptions [(["Printing", "Notations"], BoolValue True)]
    status False
    stopWorker ""
    quit'
    -}

    --When printAST goes wrong, use this:
    --rawPrintAST s
  return ()
