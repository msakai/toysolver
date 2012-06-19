module Main where

import Control.Monad
import Data.IntMap as IM
import System.Environment
import Text.Printf
import qualified Text.PBFile as PBFile

main :: IO ()
main = do
  [problemFile, modelFile] <- getArgs
  Right formula@(obj, cs) <- PBFile.parseOPBFile problemFile
  model <- liftM readModel (readFile modelFile)
  forM_ cs $ \c ->
    unless (eval model c) $
      printf "violated: %s\n" (show c)

eval :: IM.IntMap Bool -> PBFile.Constraint -> Bool
eval m (lhs, op, rhs) = op_v lhs_v rhs
  where
    lhs_v = sum [c | (c,lits) <- lhs, all (evalLit m) lits]
    op_v  = case op of
              PBFile.Ge -> (>=)
              PBFile.Eq -> (==)

evalLit :: IM.IntMap Bool -> PBFile.Lit -> Bool
evalLit m lit =
  if lit > 0
  then m IM.! lit
  else not $ m IM.! (abs lit)

readModel :: String -> IM.IntMap Bool
readModel s = IM.fromList ls2
  where
    ls = lines s
    ls2 = do
      l <- ls
      case l of
        [] -> mzero
        'v':xs -> do
          w <- words xs
          case w of
            '-':'x':ys -> return (read ys, False)
            'x':ys -> return (read ys, True)
