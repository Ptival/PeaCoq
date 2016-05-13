module XMLProtocol where

import Control.Monad.IO.Class

import Coq
import CoqIO
import CoqParse

{- Interface -}

type AboutInput = ()
type AboutOutput = CoqInfo

type AddInput = ((String, Int), (StateId, Bool))
type AddOutput = (StateId, (Either () StateId, String))

type AnnotateInput = String
type AnnotateOutput = PPXMLTree

type EditAtInput = StateId
type EditAtOutput = Either () (StateId, (StateId, StateId))

type EvarsInput = ()
type EvarsOutput = Maybe [Evar]

type GetOptionsInput = ()
type GetOptionsOutput = [([String], OptionState)]

type GoalInput = ()
type GoalOutput = Maybe Goals

type HintsInput = ()
type HintsOutput = Maybe ([[(String, String)]], [(String, String)])

type InitInput = Maybe String
type InitOutput = StateId

type InterpInput = ((Bool, Bool), String)
type InterpOutput = (StateId, Either String String)

type MkCasesInput = String
type MkCasesOutput = [[String]]

type PrintASTInput = StateId
type PrintASTOutput = CoqXMLTree

type QueryInput = (String, StateId)
type QueryOutput = String

type QuitInput = ()
type QuitOutput = ()

type SearchInput = [(SearchConstraint, Bool)]
type SearchOutput = [CoqObject String]

type SetOptionsInput = [([String], OptionValue)]
type SetOptionsOutput = ()

type StatusInput = Bool
type StatusOutput = Status

type StopWorkerInput = String
type StopWorkerOutput = ()

{- Implementation -}

about :: AboutInput -> CoqtopIO AboutOutput
about = hCall "About"

add :: AddInput -> CoqtopIO AddOutput
add input = do
  r <- hCall "Add" input
  case r of
    ValueGood (sid, _) -> do
      setStateId sid
    _ -> return ()
  return r

annotate :: AnnotateInput -> CoqtopIO AnnotateOutput
annotate = hCall "Annotate"

editAt :: EditAtInput -> CoqtopIO EditAtOutput
editAt sid = do
  o <- hCall "Edit_at" sid
  setStateId sid -- do not hoist, hCall might fail
  return o

evars :: EvarsInput -> CoqtopIO EvarsOutput
evars = hCall "Evars"

getOptions :: GetOptionsInput -> CoqtopIO GetOptionsOutput
getOptions = hCall "GetOptions"

goal :: GoalInput -> CoqtopIO GoalOutput
goal = hCall "Goal"

hints :: HintsInput -> CoqtopIO HintsOutput
hints = hCall "Hints"

init :: InitInput -> CoqtopIO InitOutput
init maybeFile = do
  r <- hCall "Init" maybeFile
  case r of
    ValueGood sid -> setStateId sid
    _ -> return ()
  return r

interp :: InterpInput -> CoqtopIO InterpOutput
interp = hCall "Interp"

mkCases :: MkCasesInput -> CoqtopIO MkCasesOutput
mkCases = hCall "MkCases"

printAST :: PrintASTInput -> CoqtopIO PrintASTOutput
printAST = hCall "PrintAst"

query :: QueryInput -> CoqtopIO QueryOutput
query = hCall "Query"

quit :: QuitInput -> CoqtopIO QuitOutput
quit () = do
  hQuery "Quit" () -- hQuery because no response is returned
  return (ValueGood ())

search :: SearchInput -> CoqtopIO SearchOutput
search = hCall "Search"

setOptions :: SetOptionsInput -> CoqtopIO SetOptionsOutput
setOptions = hCall "SetOptions"

status :: StatusInput -> CoqtopIO StatusOutput
status = hCall "Status"

stopWorker :: StopWorkerInput -> CoqtopIO StopWorkerOutput
stopWorker = hCall "StopWorker"

{- Smart methods -}

about' :: CoqtopIO AboutOutput
about' = about ()

add' :: String -> CoqtopIO AddOutput
add' s = do
  sid <- getStateId
  eid <- newEditID
  add ((s, eid), (sid, False))

evars' :: CoqtopIO EvarsOutput
evars' = evars ()

getOptions' :: CoqtopIO GetOptionsOutput
getOptions' = getOptions ()

goal' :: CoqtopIO GoalOutput
goal' = goal ()

hints' :: CoqtopIO HintsOutput
hints' = hints ()

query' :: String -> CoqtopIO QueryOutput
query' s = do
  sid <- getStateId
  query (s, sid)

quit' :: CoqtopIO ()
quit' = quit ()

{- Debug -}

rawPrintAST :: StateId -> CoqIO ()
rawPrintAST s = do
  ast <- hCallRawResponse "PrintAst" s
  liftIO . putStrLn $ ast
  return ()
