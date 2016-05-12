module Handlers.StopWorker where

import PeaCoqHandler
import XMLProtocol

handlerStopWorker :: PeaCoqHandler ()
handlerStopWorker = handleCoqtopIO stopWorker
