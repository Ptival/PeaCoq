module Handlers.SetOptions where

import PeaCoqHandler
import XMLProtocol

handlerSetOptions :: PeaCoqHandler ()
handlerSetOptions = handleCoqtopIO setOptions
