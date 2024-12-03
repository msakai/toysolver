{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE OverloadedStrings #-}
module ToySolver.Internal.JSON where

import Control.Monad
import qualified Data.Aeson as J
import qualified Data.Aeson.Types as J
import Data.Aeson ((.:))

withTypedObject :: String -> (J.Object -> J.Parser a) -> J.Value -> J.Parser a
withTypedObject name k = J.withObject name $ \obj -> do
  t <- obj .: "type"
  unless (t == name) $ fail ("expected type " ++ show name ++ ", but found type " ++ show t)
  k obj
