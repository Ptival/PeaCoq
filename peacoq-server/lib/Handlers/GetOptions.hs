module Handlers.GetOptions where

import PeaCoqHandler
import XMLProtocol

handlerGetOptions :: PeaCoqHandler ()
handlerGetOptions = handleCoqtopIO getOptions
