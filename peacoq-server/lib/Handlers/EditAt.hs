module Handlers.EditAt where

import PeaCoqHandler
import XMLProtocol

handlerEditAt :: PeaCoqHandler ()
handlerEditAt = handleCoqtopIO editAt
