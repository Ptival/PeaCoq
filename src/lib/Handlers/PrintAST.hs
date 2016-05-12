module Handlers.PrintAST where

import PeaCoqHandler
import XMLProtocol

handlerPrintAST :: PeaCoqHandler ()
handlerPrintAST = handleCoqtopIO printAST
