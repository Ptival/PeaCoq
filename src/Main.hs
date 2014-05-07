{-# LANGUAGE OverloadedStrings, RankNTypes #-}
module Main where

import Control.Applicative ((<$>), (<*), (<|>))
import Control.Monad.Catch
import Control.Monad.IO.Class
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import Data.Conduit
import Data.Conduit.Binary (sourceHandle)
import Data.Default
import Data.Maybe (fromMaybe)
import qualified Data.Text as T
import Data.XML.Types
import Snap.Core
import Snap.Util.FileServe
import Snap.Http.Server
import System.IO
import System.Process (runInteractiveCommand)
import Text.HTML.TagSoup.Entity (escapeXML)
import Text.XML.Stream.Parse

startCoqtop :: IO (Handle, Handle)
startCoqtop = do
  (hi, ho, _, _) <- runInteractiveCommand "coqtop -ideslave"
  hSetBinaryMode hi False
  hSetBuffering stdin LineBuffering
  hSetBuffering hi NoBuffering
  return (hi, ho)

main :: IO ()
main = do
  (hi, ho) <- startCoqtop
  quickHttpServe (site hi ho)

site :: Handle -> Handle -> Snap ()
site hi ho =
  ifTop (serveFile "web/rooster.html")
  <|> route [ ("query", queryHandler hi ho) ]
  <|> serveDirectory "web/"

pprintResponse :: CoqResponse [String] -> String
pprintResponse (Fail s) = s
pprintResponse (Good l) = concatMap (++ "\n") l

queryHandler :: Handle -> Handle -> Snap ()
queryHandler hi ho = do
  param <- getParam "query"
  case param of
    Nothing -> return ()
    Just queryBS -> do
      response <- liftIO $ do
        -- might want to sanitize? :3
        let query = BSC.unpack queryBS
        putStrLn $ "LOG: " ++ query
        hInterp hi query
        response <- pprintResponse <$> hForceValueResponse ho
        return response
      writeBS (BSC.pack response)

-- Parsers

type ParseXML a = Consumer Event IO a

parseCoqString :: ParseXML (Maybe String)
parseCoqString = tagNoAttr "string" (T.unpack <$> content)

parseGenericResponse :: ParseXML t -> ParseXML (Maybe (CoqResponse t))
parseGenericResponse k =
  tagName "value" (requireAttr "val" <* ignoreAttrs) $ \val ->
    case val of
      "fail" -> do
        c <- content
        return . Fail $ T.unpack c
      "good" -> do
        s <- k
        return $ Good s

data CoqResponse r
  = Fail String
  | Good r
  deriving (Eq)

instance Default (CoqResponse r) where
  def = Fail "DEFAULT"

parseValueResponse :: ParseXML (Maybe (CoqResponse [String]))
parseValueResponse = parseGenericResponse (many parseCoqString)

forceValueResponse :: ParseXML (CoqResponse [String])
forceValueResponse = force "value" parseValueResponse

xmlConduit :: (MonadThrow m) => Conduit BS.ByteString m Event
xmlConduit = parseBytes $ def { psDecodeEntities = decodeHtmlEntities }

xmlSource :: Handle -> Producer IO Event
xmlSource h = sourceHandle h $= xmlConduit

-- Handle IO

hCall :: Handle -> String -> String -> IO ()
hCall h qt q = do
  let query = "<call id=\"0\" val=\"" ++ qt ++ "\">" ++ escapeXML q ++ "</call>"
  hPutStrLn h query

hInterp :: Handle -> String -> IO ()
hInterp h = hCall h "interp"

hGoal :: Handle -> IO ()
hGoal h = hCall h "goal" ""

hForceValueResponse :: Handle -> IO (CoqResponse [String])
hForceValueResponse h = xmlSource h $$ forceValueResponse
