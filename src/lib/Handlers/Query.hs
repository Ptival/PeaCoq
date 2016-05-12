module Handlers.Query where

import PeaCoqHandler
import XMLProtocol

handlerQuery :: PeaCoqHandler ()
handlerQuery = handleCoqtopIO query

handlerQuery' :: PeaCoqHandler ()
handlerQuery' = handleCoqtopIO query'
