module Handlers.Init where

import PeaCoqHandler
import Prelude hiding (init)
import XMLProtocol

handlerInit :: PeaCoqHandler ()
handlerInit = handleCoqtopIO init
