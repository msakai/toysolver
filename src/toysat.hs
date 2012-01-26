{-# OPTIONS_GHC -Wall #-}
module Main where

import Control.Monad
import Data.Array.IArray
import qualified Data.ByteString.Lazy as BS
import qualified Data.IntMap as IM
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Char
import Data.List
import Data.Maybe
import Data.Ratio
import System.IO
import System.Environment
import System.Exit
import qualified Language.CNF.Parse.ParseDIMACS as DIMACS
import Text.Printf
import qualified SAT
import qualified PBFile
import qualified LPFile

-- ------------------------------------------------------------------------

main :: IO ()
main = do
  args <- getArgs
  case args of
    arg:args2 | map toLower arg == "--pb"     -> mainPB args2
    arg:args2 | map toLower arg == "--wbo"    -> mainWBO args2
    arg:args2 | map toLower arg == "--maxsat" -> mainMaxSAT args2
    arg:args2 | map toLower arg == "--lp"     -> mainLP args2
    _ -> mainSAT args

header :: String
header = unlines
  [ "Usage:"
  , "  toysat [file.cnf||-]"
  , "  toysat --pb [file.opb|-]"
  , "  toysat --wbo [file.wbo|-]"
  , "  toysat --maxsat [file.cnf|file.wcnf|-]"
  , "  toysat --lp [file.lp|-]"
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
  _ <- replicateM (DIMACS.numVars cnf) (SAT.newVar solver)
  forM_ (DIMACS.clauses cnf) $ \clause ->
    SAT.addClause solver (elems clause)
  result <- SAT.solve solver
  putStrLn $ "s " ++ (if result then "SATISFIABLE" else "UNSATISFIABLE")
  hFlush stdout
  when result $ do
    m <- SAT.model solver
    forM_ (IM.toList m) $ \(var,val) ->
      putStrLn ("v " ++ show (SAT.literal var val))
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
    Right formula -> solvePB formula

solvePB :: PBFile.Formula -> IO ()
solvePB formula@(obj, cs) = do
  solver <- SAT.newSolver
  let n = pbNumVars formula
  _ <- replicateM n (SAT.newVar solver)
  forM_ cs $ \(lhs, op, rhs) -> do
    let lhs' = pbConvSum lhs
    case op of
      PBFile.Ge -> SAT.addPBAtLeast solver lhs' rhs
      PBFile.Eq -> SAT.addPBExactly solver lhs' rhs

  case obj of
    Nothing -> do
      result <- SAT.solve solver
      putStrLn $ "s " ++ (if result then "SATISFIABLE" else "UNSATISFIABLE")
      hFlush stdout
      when result $ do
        m <- SAT.model solver
        pbPrintModel m

    Just obj' -> do
      result <- minimize solver (pbConvSum obj') $ \val -> do
        putStrLn $ "o " ++ show val
        hFlush stdout
      case result of
        Nothing -> do
          putStrLn $ "s " ++ "UNSATISFIABLE"
          hFlush stdout
        Just m -> do
          putStrLn $ "s " ++ "OPTIMUM FOUND"
          hFlush stdout          
          pbPrintModel m

pbConvSum :: PBFile.Sum -> [(Integer, SAT.Lit)]
pbConvSum = map f
  where
    f (w,[lit]) = (w,lit)
    f _ = error "non-linear terms are not supported"

minimize :: SAT.Solver -> [(Integer, SAT.Lit)] -> (Integer -> IO ()) -> IO (Maybe SAT.Model)
minimize solver obj update = do
  result <- SAT.solve solver
  if result
    then liftM Just loop
    else return Nothing
  where
   loop :: IO SAT.Model
   loop = do
     m <- SAT.model solver
     let v = pbEval m obj
     update v
     SAT.addPBAtMost solver obj (v - 1)
     result <- SAT.solve solver
     if result
       then loop
       else return m

pbEval :: SAT.Model -> [(Integer, SAT.Lit)] -> Integer
pbEval m xs = sum [c | (c,lit) <- xs, m IM.! SAT.litVar lit == SAT.litPolarity lit]

pbNumVars :: PBFile.Formula -> Int
pbNumVars (m, cs) = maximum (0 : vs)
  where
    vs = do
      s <- maybeToList m ++ [s | (s,_,_) <- cs]
      (_, tm) <- s
      lit <- tm
      return $ abs lit

pbPrintModel :: SAT.Model -> IO ()
pbPrintModel m = do
  forM_ (IM.toList m) $ \(var,val) ->
    putStrLn ("v " ++ (if val then "" else "-") ++ "x" ++ show var)
  hFlush stdout

-- ------------------------------------------------------------------------

mainWBO :: [String] -> IO ()
mainWBO args = do
  ret <- case args of
           ["-"]   -> fmap (PBFile.parseWBOString "-") $ hGetContents stdin
           [fname] -> PBFile.parseWBOFile fname
           _ -> hPutStrLn stderr header >> exitFailure
  case ret of
    Left err -> hPrint stderr err >> exitFailure
    Right formula -> solveWBO False formula

wboAddAtLeast :: SAT.Solver -> SAT.Lit -> [(Integer,SAT.Lit)] -> Integer -> IO ()
wboAddAtLeast solver sel lhs rhs = do
  let (lhs',rhs') = SAT.normalizePBAtLeast (lhs,rhs)
  SAT.addPBAtLeast solver ((rhs', SAT.litNot sel) : lhs') rhs'

wboAddExactly :: SAT.Solver -> SAT.Lit -> [(Integer,SAT.Lit)] -> Integer -> IO ()
wboAddExactly solver sel lhs rhs = do
  wboAddAtLeast solver sel lhs rhs
  wboAddAtLeast solver sel [(negate c, lit) | (c,lit) <- lhs] (negate rhs)

solveWBO :: Bool -> PBFile.SoftFormula -> IO ()
solveWBO isMaxSat formula@(tco, cs) = do
  solver <- SAT.newSolver
  let nvar = wboNumVars formula
  _ <- replicateM nvar (SAT.newVar solver)

  obj <- liftM concat $ forM cs $ \(cost, (lhs, op, rhs)) -> do
    let lhs' = pbConvSum lhs
    case cost of
      Nothing -> do
        case op of
          PBFile.Ge -> SAT.addPBAtLeast solver lhs' rhs
          PBFile.Eq -> SAT.addPBExactly solver lhs' rhs
        return []
      Just cost -> do
        sel <- SAT.newVar solver
        case op of
          PBFile.Ge -> wboAddAtLeast solver sel lhs' rhs
          PBFile.Eq -> wboAddExactly solver sel lhs' rhs
        return [(cost, SAT.litNot sel)]

  case tco of
    Nothing -> return ()
    Just c -> SAT.addPBAtMost solver obj (c-1)

  result <- minimize solver obj $ \val -> do
     putStrLn $ "o " ++ show val
     hFlush stdout
  case result of
    Nothing -> do
      putStrLn $ "s " ++ "UNSATISFIABLE"
      hFlush stdout
    Just m -> do
      putStrLn $ "s " ++ "OPTIMUM FOUND"
      hFlush stdout
      let m2 = IM.filterWithKey (\v _ -> v <= nvar) m
      if isMaxSat
        then maxsatPrintModel m2
        else pbPrintModel m2

wboNumVars :: PBFile.SoftFormula -> Int
wboNumVars (_, cs) = maximum vs
  where
    vs = do
      s <- [s | (_, (s,_,_)) <- cs]
      (_, tm) <- s
      lit <- tm
      return $ abs lit

-- ------------------------------------------------------------------------

type WeightedClause = (Integer, SAT.Clause)

mainMaxSAT :: [String] -> IO ()
mainMaxSAT args = do
  s <- case args of
         ["-"]   -> getContents
         [fname] -> readFile fname
         _ -> hPutStrLn stderr header >> exitFailure
  let (l:ls) = filter (not . isComment) (lines s)
  let wcnf = case words l of
        (["p","wcnf", nvar, nclause, top]) ->
          (read nvar, read top, map parseWCNFLine ls)
        (["p","wcnf", nvar, nclause]) ->
          (read nvar, 2^(63::Int), map parseWCNFLine ls)
        (["p","cnf", nvar, nclause]) ->
          (read nvar, 2, map parseCNFLine ls)
        _ -> error "parse error"
  solveMaxSAT wcnf

isComment :: String -> Bool
isComment ('c':_) = True
isComment _ = False

parseWCNFLine :: String -> WeightedClause
parseWCNFLine s =
  case map read (words s) of
    (w:xs) ->
        let ys = map fromIntegral $ init xs
        in seq w $ seqList ys $ (w, ys)
    _ -> error "parse error"

parseCNFLine :: String -> WeightedClause
parseCNFLine s = seq xs $ seqList xs $ (1, xs)
  where
    xs = init (map read (words s))

seqList :: [a] -> b -> b
seqList [] b = b
seqList (x:xs) b = seq x $ seqList xs b

solveMaxSAT :: (Int, Integer, [WeightedClause]) -> IO ()
solveMaxSAT (_, top, cs) = do
  solveWBO True
           ( Nothing
           , [ (if w >= top then Nothing else Just w
             , ([(1,[lit]) | lit<-lits], PBFile.Ge, 1))
             | (w,lits) <- cs
             ]
           )

maxsatPrintModel :: SAT.Model -> IO ()
maxsatPrintModel m = do
  forM_ (IM.toList m) $ \(var,val) ->
    putStrLn ("v " ++ show (SAT.literal var val))
  -- no terminating 0 is necessary
  hFlush stdout

-- ------------------------------------------------------------------------

mainLP :: [String] -> IO ()
mainLP args = do
  ret <- case args of
           ["-"]   -> fmap (LPFile.parseString "-") $ hGetContents stdin
           [fname] -> LPFile.parseFile fname
           _ -> hPutStrLn stderr header >> exitFailure
  case ret of
    Left err -> hPrint stderr err >> exitFailure
    Right lp -> solveLP lp

solveLP :: LPFile.LP -> IO ()
solveLP lp = do
  if not (Set.null nbvs)
    then do
      hPutStrLn stderr ("cannot handle non-binary variables: " ++ show nbvs)
      exitFailure
    else do
      solver <- SAT.newSolver

      vmap <- liftM Map.fromList $ forM (Set.toList (LPFile.binaryVariables lp)) $ \v -> do
        v2 <- SAT.newVar solver 
        return (v,v2)

      forM_ (LPFile.constraints lp) $ \(label, indicator, (lhs, op, rhs)) -> do
        when (isJust indicator) $ error "indicator constraint is not supported yet"
        let d = foldl' lcm 1 (map denominator  (rhs:[r | LPFile.Term r _ <- lhs]))
            lhs' = [(numerator (r * fromIntegral d), vmap Map.! (asSingleton vs)) | LPFile.Term r vs <- lhs]
            rhs' = numerator (rhs * fromIntegral d)
        case op of
          LPFile.Le  -> SAT.addPBAtLeast solver lhs' rhs'
          LPFile.Ge  -> SAT.addPBAtLeast solver lhs' rhs'
          LPFile.Eql -> SAT.addPBExactly solver lhs' rhs'

      let (label,obj) = LPFile.objectiveFunction lp      
          d = foldl' lcm 1 [denominator r | LPFile.Term r _ <- obj] *
              (if LPFile.dir lp == LPFile.OptMin then 1 else -1)
          obj2 = [(numerator (r * fromIntegral d), vmap Map.! (asSingleton vs)) | LPFile.Term r vs <- obj]

      result <- minimize solver obj2 $ \val -> do
        putStrLn $ "o " ++ show (fromIntegral val / fromIntegral d :: Double)
        hFlush stdout

      case result of
        Nothing -> do
          putStrLn $ "s " ++ "UNSATISFIABLE"
          hFlush stdout
        Just m -> do
          putStrLn $ "s " ++ "OPTIMUM FOUND"
          hFlush stdout
          
          forM_ (Set.toList (LPFile.binaryVariables lp)) $ \v -> do
            let val = m IM.! (vmap Map.! v)
            printf "v %s = %s\n" v (if val then "1" else "0")
          hFlush stdout
  where
    nbvs = LPFile.variables lp `Set.difference` LPFile.binaryVariables lp

    asSingleton [v] = v
    asSingleton _ = error "not a singleton"

-- ------------------------------------------------------------------------
