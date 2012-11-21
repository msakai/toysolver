{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  maxsat2lp
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------

module Main where

import Control.Monad
import System.Environment
import System.Exit
import System.IO
import qualified Text.MaxSAT as MaxSAT
import qualified Text.LPFile as LPFile
import qualified Converter.MaxSAT2LP as MaxSAT2LP

header :: String
header = "Usage: maxsat2lp [file.cnf|file.wcnf|-]"

main :: IO ()
main = do
  args <- getArgs
  ret <- case args of
            ["-"]   -> liftM MaxSAT.parseWCNFString getContents
            [fname] -> MaxSAT.parseWCNFFile fname
            _ -> hPutStrLn stderr header >> exitFailure
  case ret of
    Left err -> hPutStrLn stderr err >> exitFailure
    Right wcnf -> do
      let (lp, _) = MaxSAT2LP.convert wcnf
      case LPFile.render lp of
        Nothing -> hPutStrLn stderr "conversion failure" >> exitFailure
        Just s -> putStr s
