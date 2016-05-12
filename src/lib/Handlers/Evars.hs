module Handlers.Evars where

import PeaCoqHandler
import XMLProtocol

handlerEvars :: PeaCoqHandler ()
handlerEvars = handleCoqtopIO evars
