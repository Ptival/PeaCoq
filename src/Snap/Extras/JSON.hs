{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Snap.Extras.JSON
    (
    -- * Sending JSON Data
    writeJSON
    ) where


-------------------------------------------------------------------------------
import           Data.Aeson            as A
import           Snap.Core
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- | Mark response as 'application/json'
jsonResponse :: MonadSnap m => m ()
jsonResponse = modifyResponse $ setHeader "Content-Type" "application/json"


-------------------------------------------------------------------------------
-- | Set MIME to 'application/json' and write given object into
-- 'Response' body.
writeJSON :: (MonadSnap m, ToJSON a) => a -> m ()
writeJSON a = do
  jsonResponse
  writeLBS . encode $ a
