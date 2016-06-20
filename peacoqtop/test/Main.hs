module Main where

import Control.Monad.RWS.Strict
import Data.List                (isInfixOf)
import Prelude                  hiding (init)
import System.Exit
import System.IO
import System.Process           (runInteractiveCommand)
import Test.HUnit

import Coq
import CoqIO
import Coqtop
import XMLProtocol

pathFromCabalFileDirectoryToPluginFolder :: String
pathFromCabalFileDirectoryToPluginFolder = "plugin"

coqtop :: String
coqtop =
  "coqtop -ideslave -main-channel stdfds -async-proofs on -I "
    ++ pathFromCabalFileDirectoryToPluginFolder
    ++ " -Q "
    ++ pathFromCabalFileDirectoryToPluginFolder
    ++ " PeaCoq"

addGoalContext :: String -> CoqtopIO ()
addGoalContext s = do
  _ <- add' s
  _ <- goal'
  _ <- query' "PeaCoqGetContext."
  return (ValueGood ())

spawnAndRunCoqtopIO :: CoqtopIO a -> IO (Value a)
spawnAndRunCoqtopIO io = do
  hs <- startCoqtop coqtop
  (v, _, _) <- runRWST io hs initialCoqState
  return v

tests :: Test
tests = TestList
  [ testCoqtopVersion
  , testInit
  , testRequireList
  , testRequirePeaCoq
  ]

testCoqtopVersion :: Test
testCoqtopVersion = TestCase $ do
  (_, ho, _, _) <- runInteractiveCommand "coqtop -v"
  o <- hGetContents ho
  putStrLn coqtop
  putStrLn o
  assertBool ("coqtop version is 8.5: " ++ o) ("version 8.5" `isInfixOf` o)

testInit :: Test
testInit = TestCase $ do
  s <- spawnAndRunCoqtopIO $ do
    init Nothing
  assertEqual "Init" s (ValueGood (StateId 1))

testRequireList :: Test
testRequireList = TestCase $ do
  s <- spawnAndRunCoqtopIO $ do
    _ <- init Nothing
    add' "Require Import List."
  assertEqual "Require List" s (ValueGood (StateId 2, (Left (), "")))

testRequirePeaCoq :: Test
testRequirePeaCoq = TestCase $ do
  s <- spawnAndRunCoqtopIO $ do
    _ <- init Nothing
    add' "Require Import PeaCoq.PeaCoq."
  assertEqual "Require PeaCoq" s (ValueGood (StateId 2, (Left (), "")))

main :: IO Counts
main = do
  r <- runTestTT tests
  let nbErrors = errors r + failures r
  exitWith $ if nbErrors == 0 then ExitSuccess else ExitFailure 1
