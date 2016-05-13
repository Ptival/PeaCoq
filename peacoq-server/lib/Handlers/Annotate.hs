module Handlers.Annotate where

import PeaCoqHandler
import XMLProtocol

handlerAnnotate :: PeaCoqHandler ()
handlerAnnotate = handleCoqtopIO annotate
