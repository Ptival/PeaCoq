module Handlers.Quit where

import PeaCoqHandler
import XMLProtocol

handlerQuit :: PeaCoqHandler ()
handlerQuit = handleCoqtopIO quit
