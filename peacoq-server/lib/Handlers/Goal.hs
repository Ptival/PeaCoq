module Handlers.Goal where

import PeaCoqHandler
import XMLProtocol

handlerGoal :: PeaCoqHandler ()
handlerGoal = handleCoqtopIO goal
