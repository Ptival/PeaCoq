module Handlers.MkCases where

import PeaCoqHandler
import XMLProtocol

handlerMkCases :: PeaCoqHandler ()
handlerMkCases = handleCoqtopIO mkCases
