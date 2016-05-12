module Main where

-- import Control.Monad.Loops ()
import Control.Monad.RWS.Strict
import Data.List                (isInfixOf)
import Prelude                  hiding (init)
import System.Exit
import System.IO
import System.Process           (runInteractiveCommand)
import Test.HUnit

import Coq.StateId
import Coq.Value
import CoqIO
import PeaCoqHandler
import XMLProtocol

coqtop :: String
coqtop = "coqtop -ideslave -main-channel stdfds -I plugin/ -Q plugin/ PeaCoq"

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
  assertBool "coqtop version is 8.5" ("version 8.5" `isInfixOf` o)

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

-- main :: IO ()
-- main = do
--   hs <- startCoqtop coqtop
--   void $ runRWST (io hs) hs initialCoqState
--   where
--     io :: Handles -> CoqtopIO ()
--     io (_, _, _he, _ph) = do
--       s <- init Nothing
--       liftIO . putStrLn $ show s
--       -- _ <- init Nothing
--       -- _ <- editAt (StateId 1)
--       -- _ <- add' "Require Import PeaCoq.PeaCoq."
--       -- _ <- hQuery "Add" "Require Import ZArith."
--       -- _ <- hQuery "Goal" ()
--       -- _ <- hQuery "Add" "PeaCoqGetContext."
--       -- mapM_ addGoalContext
--       --   [ "Require Import ZArith."
--       --   ]
--       -- status False
--       -- editAt (StateId 1)
--       -- add' "Require Import ZArith."
--       --status False
--       --editAt (StateId 1)
--       --add' "Require Import ZArith."
--       -- add' "Require Import PeaCoq.PeaCoq."
--       -- add' "Require Import List."
--       -- add' "Import ListNotations."
--       -- add' "Theorem t : [0] = [1]."
--       -- add' "Definition admit {T : Type} : T."
--       -- add' "Admitted."
--       -- status False
--       return (ValueGood ())
--
-- {-
--       sid <- getStateId
--       eid <- newEditID
--       r <- hCallRawResponse "Add" (("Import ListNotations.", eid), (sid, False))
--       liftIO $ do
--         putStrLn $ "Raw response: " ++ r
--         --putStrLn $ show (r :: Value AddOutput)
--         exit <- waitForProcess ph
--         putStrLn $ show exit
--       return (ValueGood ())
-- -}
