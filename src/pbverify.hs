module Main where

import Control.Monad
import Data.Array.IArray
import System.Environment
import Text.Printf
import qualified Text.PBFile as PBFile
import SAT.Types

main :: IO ()
main = do
  [problemFile, modelFile] <- getArgs
  Right formula@(obj, cs) <- PBFile.parseOPBFile problemFile
  model <- liftM readModel (readFile modelFile)
  forM_ cs $ \c ->
    unless (eval model c) $
      printf "violated: %s\n" (show c)

eval :: Model -> PBFile.Constraint -> Bool
eval m (lhs, op, rhs) = op_v lhs_v rhs
  where
    lhs_v = sum [c | (c,lits) <- lhs, all (evalLit m) lits]
    op_v  = case op of
              PBFile.Ge -> (>=)
              PBFile.Eq -> (==)

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
            '-':'x':ys -> return (read ys, False)
            'x':ys -> return (read ys, True)
        _ -> mzero

