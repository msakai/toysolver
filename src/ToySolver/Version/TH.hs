{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}
module ToySolver.Version.TH
  ( gitHashQ
  , compilationTimeQ
  ) where

import Control.Exception
import Control.Monad
import Data.Time
import System.Process
import Language.Haskell.TH

getGitHash :: IO (Maybe String)
getGitHash =
  liftM (Just . takeWhile (/='\n')) (readProcess "git" ["rev-parse", "--short", "HEAD"] "")
  `catch` \(_::SomeException) -> return Nothing
 
gitHashQ :: ExpQ
gitHashQ = do
  m <- runIO getGitHash
  case m of
    Nothing -> [| Nothing |]
    Just s -> [| Just |] `appE` litE (stringL s)

compilationTimeQ :: ExpQ
compilationTimeQ = do
  tm <- runIO getCurrentTime
  [| read $(litE (stringL (show tm))) :: UTCTime |]
