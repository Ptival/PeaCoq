module Handlers.Status where

import PeaCoqHandler
import XMLProtocol

handlerStatus :: PeaCoqHandler ()
handlerStatus = handleCoqtopIO status
