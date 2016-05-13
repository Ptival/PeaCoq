module Handlers.Hints where

import PeaCoqHandler
import XMLProtocol

handlerHints :: PeaCoqHandler ()
handlerHints = handleCoqtopIO hints
