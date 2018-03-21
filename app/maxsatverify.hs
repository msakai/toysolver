{-# LANGUAGE CPP #-}
module Main where

import Control.Monad
import Data.Array.IArray
import Data.IORef
import System.Environment
import Text.Printf
import qualified ToySolver.Text.WCNF as WCNF
import ToySolver.SAT.Types
import ToySolver.Internal.Util (setEncodingChar8)

main :: IO ()
main = do
#ifdef FORCE_CHAR8
  setEncodingChar8
#endif

  [problemFile, modelFile] <- getArgs
  Right wcnf <- WCNF.parseFile problemFile
  model <- liftM readModel (readFile modelFile)
  costRef <- newIORef 0
  forM_ (WCNF.wcnfClauses wcnf) $ \(w,c) ->
    unless (eval model c) $
      if w == WCNF.wcnfTopCost wcnf
      then printf "violated hard constraint: %s\n" (show c)
      else do
        tc <- readIORef costRef
        writeIORef costRef $! tc + w
  printf "total cost = %d\n" =<< readIORef costRef

eval :: Model -> PackedClause -> Bool
eval m lits = or [evalLit m lit | lit <- unpackClause lits]

readModel :: String -> Model
readModel s = array (1, maximum (0 : map fst ls2)) ls2
  where
    ls = lines s
    ls2 = do
      l <- ls
      case l of
        'v':xs -> do
          w <- words xs
          case w of
            '-':ys -> return (read ys, False)
            ys -> return (read ys, True)
        _ -> mzero

