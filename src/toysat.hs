module Main where

import Control.Monad
import Data.Array.IArray
import qualified Data.ByteString.Lazy as BS
import qualified Data.IntMap as IM
import Data.Char
import Data.Maybe
import System.IO
import System.Environment
import System.Exit
import qualified Language.CNF.Parse.ParseDIMACS as DIMACS
import qualified SAT
import qualified PBFile

-- ------------------------------------------------------------------------

main :: IO ()
main = do
  args <- getArgs
  case args of
    arg:args2 | map toLower arg == "--pb" -> mainPB args2
    _ -> mainSAT args

header :: String
header = unlines
  [ "Usage:"
  , "  toysat [file.cnf||-]"
  , "  toysat --pb [file.opb|-]"
  ]

-- ------------------------------------------------------------------------

mainSAT :: [String] -> IO ()
mainSAT args = do
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
  hFlush stdout
  when result $ do
    m <- SAT.model solver  
    forM_ (IM.toList m) $ \(var,val) -> putStrLn ("v " ++ show (SAT.literal var val))
    putStrLn "v 0"
    hFlush stdout

-- ------------------------------------------------------------------------

mainPB :: [String] -> IO ()
mainPB args = do
  ret <- case args of
           ["-"]   -> fmap (PBFile.parseOPBString "-") $ hGetContents stdin
           [fname] -> PBFile.parseOPBFile fname
           _ -> hPutStrLn stderr header >> exitFailure
  case ret of
    Left err -> hPrint stderr err >> exitFailure
    Right cnf -> solvePB cnf

solvePB :: PBFile.Formula -> IO ()
solvePB formula@(obj, cs) = do
  solver <- SAT.newSolver
  let n = pbNumVars formula
  vs <- replicateM n (SAT.newVar solver)
  forM cs $ \(lhs, op, rhs) -> do
    let lhs' = pbConvSum lhs
    case op of
      PBFile.Ge -> SAT.addPBAtLeast solver lhs' rhs
      PBFile.Eq -> SAT.addPBExactly solver lhs' rhs

  result <- SAT.solve solver
  case obj of
    Nothing -> do
      putStrLn $ "s " ++ (if result then "SATISFIABLE" else "UNSATISFIABLE")
      hFlush stdout
      when result $ do
        m <- SAT.model solver  
        forM_ (IM.toList m) $ \(var,val) ->
          putStrLn ("v " ++ show (SAT.literal var val))
        -- putStrLn "v 0" -- NO terminating 0 is required for PB
        hFlush stdout
    Just obj' -> do
      if not result
        then putStrLn $ "s " ++ "UNSATISFIABLE"
        else pbOpt solver (pbConvSum obj')

pbConvSum :: PBFile.Sum -> [(Integer, SAT.Lit)]
pbConvSum = map f
  where
    f (w,[lit]) = (w,lit)
    f _ = error "non-linear terms are not supported"

pbOpt :: SAT.Solver -> [(Integer, SAT.Lit)] -> IO ()
pbOpt solver obj = do
  m <- loop
  putStrLn $ "s " ++ "OPTIMUM FOUND"
  hFlush stdout
  let v = eval m obj
  putStrLn $ "o " ++ show v
  forM_ (IM.toList m) $ \(var,val) ->
    putStrLn ("v " ++ show (SAT.literal var val))
  -- putStrLn "v 0" -- NO terminating 0 is required for PB
  hFlush stdout

  where
   loop :: IO SAT.Model
   loop = do
     m <- SAT.model solver
     let v = eval m obj
     putStrLn $ "o " ++ show v
     hFlush stdout
     SAT.addPBAtMost solver obj (v - 1)
     result <- SAT.solve solver
     if result
       then loop
       else return m

   eval :: SAT.Model -> [(Integer, SAT.Lit)] -> Integer
   eval m xs = sum [c | (c,lit) <- xs, m IM.! SAT.litVar lit == SAT.litPolarity lit]

pbNumVars :: PBFile.Formula -> Int
pbNumVars (m, cs) = maximum vs
  where
    vs = do
      s <- maybeToList m ++ [s | (s,_,_) <- cs]
      (_, tm) <- s
      lit <- tm
      return $ abs lit

-- ------------------------------------------------------------------------
