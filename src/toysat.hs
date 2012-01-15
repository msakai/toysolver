module Main where

import Control.Monad
import Data.Array.IArray
import qualified Data.ByteString.Lazy as BS
import qualified Data.IntMap as IM
import System.IO
import System.Environment
import System.Exit
import qualified Language.CNF.Parse.ParseDIMACS as DIMACS
import qualified SAT

main :: IO ()
main = do
  args <- getArgs
  ret <- case args of
           ["-"]   -> fmap (DIMACS.parseByteString "-") $ BS.hGetContents stdin
           [fname] -> DIMACS.parseFile fname
           _ -> hPutStrLn stderr header >> exitFailure
  case ret of
    Left err -> hPrint stderr err >> exitFailure
    Right cnf -> solveCNF cnf

solveCNF :: DIMACS.CNF -> IO ()
solveCNF cnf = do
  solver <- SAT.newSolver
  vs <- replicateM (DIMACS.numVars cnf) (SAT.newVar solver)
  forM (DIMACS.clauses cnf) $ \clause ->
    SAT.addClause solver (elems clause)
  result <- SAT.solve solver
  putStrLn $ "s " ++ (if result then "SATISFIABLE" else "UNSATISFIABLE")
  m <- SAT.model solver  
  forM_ (IM.toList m) $ \(var,val) -> putStrLn ("v " ++ show (SAT.literal var val))
  putStrLn "v 0"

header :: String
header = "Usage: toysat2lp [file.cnf|-]"
