{-# LANGUAGE ScopedTypeVariables, TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}
module ToySolver.Internal.GitHash (gitHashQ) where

import Control.Exception
import Control.Monad
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
