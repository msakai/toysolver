{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}
module Main where

import Control.Applicative hiding (many)
import Control.Monad
import Data.Array.IArray
import qualified Data.ByteString.Lazy.Char8 as BL
import Data.Default.Class
import Data.List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.PseudoBoolean as PB
import Data.Set (Set)
import qualified Data.Set as Set
import System.Console.GetOpt
import System.Environment
import System.Exit
import System.IO
import Text.Parsec hiding (try)
import qualified Text.Parsec.ByteString.Lazy as ParsecBL
import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.PBO as PBO
import qualified ToySolver.SAT.Store.PB as PBStore

data Problem
  = Problem
  { probSize :: (Int,Int)
  , probLineNum :: Int
  , probLines :: [(Number, Cell, Cell)]
  }
  deriving (Show)

type Number = Int
type Cell = (Int,Int)
type Edge = (Cell, Cell)

parser ::  Stream s m Char => ParsecT s u m Problem
parser = do
  _ <- string "SIZE"
  spaces
  w <- num
  _ <- char 'X'
  h <- num
  _ <- endOfLine
  
  _ <- string "LINE_NUM"
  spaces
  n <- num
  _ <- endOfLine

  xs <- many $ do
    _ <- string "LINE#"
    i <- num
    spaces
    src <- cell
    _ <- char '-'
    dst <- cell
    _ <- endOfLine
    return (i,src,dst)

  return $ Problem (w,h) n xs
    
  where
    num = read <$> many digit

    cell = do
      _ <- char '('
      x <- num
      _ <- char ','
      y <- num
      _ <- char ')'
      return (x,y)

type Encoded = (Array Cell (Array Number SAT.Var), Map Edge SAT.Var)

encode :: SAT.AddPBLin m enc => enc -> Options -> Problem -> m Encoded
encode enc opt Problem{ probSize = (w,h), probLineNum = n, probLines = ls } = do
  let bnd = ((0,0), (w-1,h-1))
      cells = range bnd
      edges = [(a,b) | a@(x,y) <- cells, b <- [(x+1,y),(x,y+1)], inRange bnd b]
      adjacentEdges a@(x,y) =
        [(a,b) | b <- [(x+1,y),(x,y+1)], inRange bnd b] ++
        [(b,a) | b <- [(x-1,y),(x,y-1)], inRange bnd b]
      ks = [1..n]

  -- 各マスへの数字の割り当てを表す変数 (0 は数字なしを表す)
  vs <- liftM (array bnd) $ forM cells $ \(x,y) -> do
    let r = if optAssumeNoBlank opt
            then (1,n)
            else (0,n)
    zs <- liftM (array r) $ forM (range r) $ \k -> do
      v <- SAT.newVar enc
      return (k,v)
    return ((x,y), zs)
  -- 各辺の有無を表す変数
  evs <- liftM Map.fromList $ forM edges $ \e -> do
    v <- SAT.newVar enc
    return (e,v)

  -- 初期数字
  let m0 = Map.fromList [(c,k) | (k,src,dst) <- ls, c <- [src,dst]]
  forM_ (Map.toList m0) $ \(c,k) -> do
    SAT.addClause enc [vs!c!k]

  -- 各マスには高々ひとつしか数字が入らない
  forM_ (range bnd) $ \a -> do
    SAT.addExactly enc [v | v <- elems (vs!a)] 1
  -- 辺で連結されるマスは同じ数字
  forM_ (Map.toList evs) $ \((a,b),v) ->
    forM_ ks $ \k -> do
      SAT.addClause enc [-v, -(vs!a!k), vs!b!k]
      SAT.addClause enc [-v, -(vs!b!k), vs!a!k]

  -- 初期数字の入っているマスの次数は1
  forM_ (Map.toList m0) $ \(a,_) -> do
    SAT.addExactly enc [evs Map.! e | e <- adjacentEdges a] 1
  -- 初期数字の入っていないマスの次数は0か2
  forM_ (range bnd) $ \a -> do
    when (a `Map.notMember` m0) $ do
      if optAssumeNoBlank opt then do
        SAT.addExactly enc [evs Map.! e | e <- adjacentEdges a] 2
      else do
        let v = vs!a!0
        -- v → deg(a)=0
        -- SAT.addPBAtMostSoft enc v [(1, evs Map.! e) | e <- adjacentEdges a] 0
        forM_ (adjacentEdges a) $ \e -> SAT.addClause enc [-v, -(evs Map.! e)]     
        -- ¬v → deg(a)=2
        SAT.addPBExactlySoft enc (-v) [(1, evs Map.! e) | e <- adjacentEdges a] 2
        -- ¬v → deg(a)>0
        -- SAT.addClause enc $ v : [evs Map.! e | e <- adjacentEdges a]

  -- 同一数字のマスが４個、田の字に凝ってはいけない
  when (optAssumeNoDetour opt) $ do
    forM_ [0..w-2] $ \x -> do
      forM_ [0..h-2] $ \y -> do
        let a = (x,y)
            b = (x+1, y)
            c = (x, y+1)
            d = (x+1,y+1)
        SAT.addAtMost enc [evs Map.! e | e <- [(a,b),(a,c),(b,d),(c,d)]] 2

  return (vs, evs)

type Solution = (Map Cell Number, Set Edge)

decode :: Problem -> Encoded -> SAT.Model -> Solution
decode prob (vs, evs) m = (solCells, solEdges)
  where
    solCells = Map.fromList $ do
      a@(x,y) <- range (bounds vs)
      guard $ a `Set.member` usedCells
      case [k | (k,v) <- assocs (vs!(x,y)), SAT.evalLit m v] of
        k:_ -> return ((x,y),k)
        [] -> mzero
    solEdges = Set.fromList [e | e@(a,_) <- edges, a `Set.member` usedCells]
    
    edges = [e | (e,ev) <- Map.toList evs, SAT.evalLit m ev]
    adjacents = Map.fromListWith Set.union $ concat $ [[(a, Set.singleton b), (b, Set.singleton a)] | (a,b) <- edges]
    usedCells = Set.unions [g a (Set.singleton a) | (_k,a,_b) <- probLines prob]
      where
        g a visited =
          case Set.toList (Map.findWithDefault Set.empty a adjacents Set.\\ visited) of
            [] -> visited
            b:_ -> g b (Set.insert b visited)

createSolver :: Options -> Problem -> IO (IO (Maybe Solution))
createSolver opt prob = do
  solver <- SAT.newSolver
  SAT.setLogger solver $ hPutStrLn stderr
  encoded <- encode solver opt prob
  unless (optAssumeNoBlank opt) $ do
    forM_ (elems (fst encoded)) $ \xs -> do
      SAT.setVarPolarity solver (xs!0) False
  let m = do
        ret <- SAT.solve solver
        if ret then do
          m <- SAT.getModel solver
          let sol = decode prob encoded m
          SAT.addClause solver $ blockingClause prob encoded sol
          return $ Just sol
        else
          return Nothing
  return m

printSolution :: Problem -> Solution -> IO ()
printSolution prob (cells, _) = do
  let (w,h) = probSize prob
  forM_ [0 .. h-1] $ \y -> do
    putStrLn $ concat $ intersperse ","
     [ case Map.lookup (x,y) cells of
         Nothing -> replicate width '0'
         Just k -> replicate (width - length (show k)) '0' ++ show k
     | x <- [0 .. w-1]
     ]
  where
    width = length $ show (probLineNum prob)

blockingClause :: Problem -> Encoded -> Solution -> SAT.Clause
blockingClause _prob (_,edgesEnc) (_,edges) = [- (edgesEnc Map.! e) | e <- Set.toList edges]

data Options
  = Options
  { optOptimize :: Bool
  , optAssumeNoBlank :: Bool
  , optAssumeNoDetour :: Bool
  , optNumSolutions :: Int
  }

instance Default Options where
  def =
    Options
    { optOptimize = False
    , optAssumeNoBlank = False
    , optAssumeNoDetour = False
    , optNumSolutions = 1
    }

options :: [OptDescr (Options -> Options)]
options =
    [ Option [] ["optimize"]
        (NoArg (\opt -> opt{ optOptimize = True }))
        "Minimize line length and turnarounds (-n option will be ignored)"
    , Option [] ["no-blank"]
        (NoArg (\opt -> opt{ optAssumeNoBlank = True }))
        "Assume no blank cells in solution"
    , Option [] ["no-detour"]
        (NoArg (\opt -> opt{ optAssumeNoDetour = True }))
        "Assume no detour in solution"
    , Option ['n'] []
        (ReqArg (\val opt -> opt{ optNumSolutions = read val }) "<int>")
        "Maximal number of solutions to enumerate, or negative value for all solutions (default: 1)"
    ]

header :: String
header = unlines
  [ "Usage:"
  , "  numberlink [OPTION]... problem.txt"
  , "  numberlink [OPTION]... problem.txt encoded.opb"
  , ""
  , "Options:"
  ]

showHelp :: Handle -> IO ()
showHelp h = hPutStrLn h (usageInfo header options)

main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    (_,_,errs@(_:_)) -> do
      mapM_ putStrLn errs
      exitFailure
    (o,args2,[]) -> do
      let opt = foldl (flip id) def o
      case args2 of
        [fname] -> do
          r <- ParsecBL.parseFromFile parser fname
          case r of
            Left err -> error (show err)
            Right prob@Problem{ probSize = (w,h) } -> do
              putStrLn $ "SIZE " ++ show w ++ " " ++ show h
              if not (optOptimize opt) then do                
                solve <- createSolver opt prob
                let loop n
                      | n == 0 = return ()
                      | otherwise = do
                          m <- solve
                          case m of
                            Nothing -> return ()
                            Just sol -> do
                              printSolution prob sol
                              putStrLn ""
                              loop (if n > 0 then n - 1 else n)
                loop (optNumSolutions opt)
              else do
                solver <- SAT.newSolver
                SAT.setLogger solver $ hPutStrLn stderr
                encoded@(cells,edges) <- encode solver opt prob
                unless (optAssumeNoBlank opt) $ do
                  forM_ (elems cells) $ \xs -> do
                    SAT.setVarPolarity solver (xs!0) False
                let obj1 = [(1,v) | v <- Map.elems (snd encoded)]
                obj2 <- liftM concat $ forM (range ((0,0), (w-2,h-2))) $ \a@(x,y) -> do
                  let b = (x+1,y)
                      c = (x,y+1)
                      d = (x+1,y+1)
                  abd <- SAT.newVar solver
                  SAT.addClause solver [- (edges Map.! (a,b)), - (edges Map.! (b,d)), abd]
                  acd <- SAT.newVar solver
                  SAT.addClause solver [- (edges Map.! (a,c)), - (edges Map.! (c,d)), acd]
                  cab <- SAT.newVar solver
                  SAT.addClause solver [- (edges Map.! (a,c)), - (edges Map.! (a,b)), cab]
                  bdc <- SAT.newVar solver
                  SAT.addClause solver [- (edges Map.! (b,d)), - (edges Map.! (c,d)), bdc]
                  return [(1,abd), (1,acd), (1,cab), (1,bdc)]
                let obj = obj1 ++ obj2
                pbo <- PBO.newOptimizer solver obj
                PBO.setLogger pbo $ hPutStrLn stderr
                PBO.setOnUpdateBestSolution pbo $ \m val -> do
                  hPutStrLn stderr $ "# obj = " ++ show val
                  hFlush stderr
                  let sol = decode prob encoded m
                  printSolution prob sol
                  putStrLn ""
                  hFlush stdout
                PBO.optimize pbo

        [fname, fname2] -> do
          r <- ParsecBL.parseFromFile parser fname
          case r of
            Left err -> error (show err)
            Right prob -> do
              store <- PBStore.newPBStore
              _encoded <- encode store opt prob
              opb <- PBStore.getPBFormula store
              PB.writeOPBFile fname2 opb
        _ -> do
          showHelp stderr

sampleFile :: BL.ByteString
sampleFile = BL.unlines
  [ "SIZE 15X15"
  , "LINE_NUM 12"
  , "LINE#1 (10,0)-(4,14)"
  , "LINE#2 (9,5)-(9,14)"
  , "LINE#3 (2,7)-(4,12)"
  , "LINE#4 (2,5)-(7,13)"
  , "LINE#5 (2,4)-(4,10)"
  , "LINE#6 (2,2)-(5,5)"
  , "LINE#7 (6,5)-(5,10)"
  , "LINE#8 (5,0)-(7,9)"
  , "LINE#9 (10,2)-(12,7)"
  , "LINE#10 (7,1)-(12,9)"
  , "LINE#11 (9,8)-(12,12)"
  , "LINE#12 (8,9)-(12,10)"
  ]

sample :: Problem
Right sample = parse parser "sample" sampleFile
