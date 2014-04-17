module Main where

import Control.Monad
import Data.Array.IArray
import Text.Printf
import Criterion.Main
import qualified Language.CNF.Parse.ParseDIMACS as DIMACS
import qualified SAT

solve :: FilePath -> IO ()
solve fname = do
  ret <- DIMACS.parseFile fname
  case ret of
    Left err  -> error $ show err
    Right cnf -> do
      solver <- SAT.newSolver
      SAT.setRandomFreq solver 0
      _ <- replicateM (DIMACS.numVars cnf) (SAT.newVar solver)
      forM_ (DIMACS.clauses cnf) $ \clause ->
        SAT.addClause solver (elems clause)
      SAT.solve solver
      return ()

main :: IO ()
main = do
  Criterion.Main.defaultMain
    [ bgroup "uf250-1065"
        [ bench fname (solve path)
        | i <- [(1::Int)..100]
        , let fname = printf "uf250-0%d.cnf" i
        , let path = "benchmarks/UF250.1065.100/" ++ fname
        ]
    , bgroup "uuf250-1065"
        [ bench fname (solve path)
        | i <- [(1::Int)..100]
        , let fname = printf "uuf250-0%d.cnf" i
        , let path = "benchmarks/UUF250.1065.100/" ++ fname
        ]
    ]
