module Handlers.Add where

import PeaCoqHandler
import XMLProtocol

handlerAdd :: PeaCoqHandler ()
handlerAdd = handleCoqtopIO add

handlerAdd' :: PeaCoqHandler ()
handlerAdd' = handleCoqtopIO add'
