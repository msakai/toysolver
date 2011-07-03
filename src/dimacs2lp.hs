module Main where

import qualified Data.ByteString.Lazy as BS
import Data.Array.IArray
import qualified Data.Set as Set
import qualified Data.Map as Map
import System.IO
import System.Environment
import System.Exit

import LPFile
import qualified Language.CNF.Parse.ParseDIMACS as DIMACS

cnfToLP :: DIMACS.CNF -> LPFile.LP
cnfToLP cnf
  = LP
  { variables = Set.fromList vs
  , isMinimize = False
  , objectiveFunction = (Nothing, foldr1 (:+:) (map Var vs))
  , constraints = cs
  , LPFile.bounds = Map.empty
  , integerVariables = Set.empty
  , binaryVariables = Set.fromList vs
  , semiContinuousVariables = Set.empty
  , sos = []
  }
  where
    vs = ["x" ++ show i | i <- [1 .. DIMACS.numVars cnf]]
    cs = do
      cl <- DIMACS.clauses cnf      
      let (lhs,n) = foldr f (Const 0, 0) (elems cl)
      return (Nothing, Nothing, (lhs, Ge, fromIntegral $ 1 - n))
    f :: Int -> (Expr,Integer) -> (Expr,Integer)
    f i (vs,n) =
      if i > 0
      then (Var v :+: vs, n)
      else (Const (negate 1) :*: Var v :+: vs, n+1)
      where v = "x" ++ show (abs i)

main :: IO ()
main = do
  args <- getArgs
  ret <- case args of
           ["-"]   -> fmap (DIMACS.parseByteString "-") $ BS.hGetContents stdin
           [fname] -> DIMACS.parseFile fname
           _ -> hPutStrLn stderr header >> exitFailure
  case ret of
    Left err -> hPrint stderr err >> exitFailure
    Right cnf ->
      case LPFile.render (cnfToLP cnf) of
        Nothing -> hPutStrLn stderr "conversion failure" >> exitFailure
        Just s2 -> putStr s2

header :: String
header = "Usage: dimacs2lp [file.cnf|-]"
