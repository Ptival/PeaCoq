module Handlers.About where

import PeaCoqHandler
import XMLProtocol

handlerAbout :: PeaCoqHandler ()
handlerAbout = handleCoqtopIO about
