module Handlers.Interp where

import PeaCoqHandler
import XMLProtocol

handlerInterp :: PeaCoqHandler ()
handlerInterp = handleCoqtopIO interp
