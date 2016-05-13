module Handlers.Search where

import PeaCoqHandler
import XMLProtocol

handlerSearch :: PeaCoqHandler ()
handlerSearch = handleCoqtopIO search
