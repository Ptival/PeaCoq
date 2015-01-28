{-# Language OverloadedStrings #-}

--import Control.Applicative
import Control.Monad.IO.Class
import Test.HUnit
import Test.WebDriver
--import Test.WebDriver.Capabilities
--import Test.WebDriver.Commands
import System.IO

wdconfig :: WDConfig
wdconfig = defaultConfig

runTests :: IO (Counts, Int)
runTests = runTestText (putTextToHandle stderr False) allTests

allTests :: Test
allTests = TestList
  [ TestLabel "testEditor" testEditor
  ]

testEditor :: Test
testEditor = TestCase . assert $
  runSession wdconfig $ do
    openPage "http://localhost:4242"
    element <- findElem $ ById "editor"
    text <- getText element
    liftIO . putStrLn $ "Text: " ++ show text
    return $ text == "(* Your code here *)"
