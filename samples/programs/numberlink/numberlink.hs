{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}
module Main where

import Control.Monad
import Data.Array.IArray
import qualified Data.ByteString.Lazy.Char8 as BL
import Data.Char
import Data.Default.Class
import Data.List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import qualified Data.PseudoBoolean as PB
import Data.Set (Set)
import qualified Data.Set as Set
import System.Console.GetOpt
import System.Environment
import System.Exit
import System.IO
import Text.Parsec hiding (try)
import qualified Text.Parsec.ByteString.Lazy as ParsecBL
import qualified ToySolver.FileFormat as FF
import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.PBO as PBO
import qualified ToySolver.SAT.Store.PB as PBStore

data Problem
  = Problem
  { probSize :: (Int,Int,Int)
  , probIsMultiLayer :: Bool
  , probLineNum :: Int
  , probLines :: [(Number, Cell, Cell)]
  , probVias :: [(Via, [Cell])]
  }
  deriving (Show)

type Number = Int
type Cell = (Int,Int,Int)
type Edge = (Cell, Cell)
type Via = String

parser ::  Stream s m Char => ParsecT s u m Problem
parser = do
  optional $ string "\xEF\xBB\xBF" -- BOM in UTF-8
  spaces
  _ <- string "SIZE"
  spaces
  w <- num
  _ <- char 'X'
  h <- num
  dd <- optionMaybe $ char 'X' >> num
  let (d,isMultiLayer) =
        case dd of
          Nothing -> (1, False)
          Just d -> (d, True)
  _ <- endOfLine

  let cell = do
        _ <- char '('
        x <- num
        _ <- char ','
        y <- num
        z <-
          if isMultiLayer then do
            _ <- char ','
            num
          else
            return 1
        _ <- char ')'
        spaces
        return (x,y,z)

  _ <- string "LINE_NUM"
  spaces
  n <- num
  _ <- endOfLine

  xs <- many $ do
    _ <- string "LINE#"
    i <- num
    spaces
    src <- cell
    optional $ char '-' >> spaces
    dst <- cell
    return (i,src,dst)

  ys <- many $ do
    _ <- string "VIA#"
    v <- many letter
    spaces
    cs <- cell `sepBy` optional (char '-' >> spaces)
    return (v,cs)

  return $ Problem (w,h,d) (isJust dd) n xs ys

  where
    num = read <$> many digit

type Encoded = (Array Cell (Array Number SAT.Var), Map Edge SAT.Var)

encode :: SAT.AddPBLin m enc => enc -> Options -> Problem -> m Encoded
encode enc opt Problem{ probSize = (w,h,d), probLineNum = n, probLines = ls, probVias = vias } = do
  let bnd = ((0,0,1), (w-1,h-1,d))
      cells = range bnd
      edges = [(a,b) | a@(x,y,z) <- cells, b <- [(x+1,y,z),(x,y+1,z)], inRange bnd b]
      adjacentEdges a@(x,y,z) =
        [(a,b) | b <- [(x+1,y,z),(x,y+1,z)], inRange bnd b] ++
        [(b,a) | b <- [(x-1,y,z),(x,y-1,z)], inRange bnd b]
      ks = [1..n]

  -- ビアへの数字の割当を表す変数 (0 は数字なしを表す)
  viaVs <- liftM Map.fromList $ forM vias $ \(via, _) -> do
    let r = if optAssumeNoBlank opt
            then (1,n)
            else (0,n)
    zs <- liftM (array r) $ forM (range r) $ \k -> do
      v <- SAT.newVar enc
      return (k,v)
    return (via, zs)
  let viaPos = Map.fromList [(a,via) | (via,as) <- vias, a <- as]

  -- 各マスへの数字の割り当てを表す変数 (0 は数字なしを表す)
  vs <- liftM (array bnd) $ forM cells $ \a -> do
    case Map.lookup a viaPos of
      Just via -> return (a, viaVs Map.! via)
      Nothing -> do
        let r = if optAssumeNoBlank opt
                then (1,n)
                else (0,n)
        zs <- liftM (array r) $ forM (range r) $ \k -> do
          v <- SAT.newVar enc
          return (k,v)
        return (a, zs)
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
  forM_ (Map.toList evs) $ \((a,b),v) ->
    forM_ ks $ \k -> do
      -- 辺で連結されるマスは同じ数字
      SAT.addClause enc [-v, -(vs!a!k), vs!b!k]
      SAT.addClause enc [-v, -(vs!b!k), vs!a!k]
      -- 連結されない隣接マスは違う数字
      when (optAssumeNoDetour opt) $
        SAT.addClause enc [v, -(vs!a!k), -(vs!b!k)]

  forM_ (range bnd) $ \a -> do
    if a `Map.member` m0 then do
      -- 初期数字の入っているマスの次数は1
      SAT.addExactly enc [evs Map.! e | e <- adjacentEdges a] 1
    else if a `Map.member` viaPos then do
      -- ビアの次数は高々1 (ADC2016ルールでも中間層は0になるので注意)
      SAT.addAtMost enc [evs Map.! e | e <- adjacentEdges a] 1
    else do
      -- 初期数字の入っていないマスの次数は0か2
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

  -- コの字の禁止
  when (optAssumeNoDetour opt) $ do
    forM_ [1..d] $ \z -> do
      forM_ [0..w-2] $ \x -> do
        forM_ [0..h-2] $ \y -> do
          let a = (x, y, z)
              b = (x+1, y, z)
              c = (x, y+1, z)
              d = (x+1, y+1, z)
          SAT.addAtMost enc [evs Map.! e | e <- [(a,b),(a,c),(b,d),(c,d)]] 2

  -- https://kaigi.org/jsai/webprogram/2016/pdf/67.pdf の追加成約
  when (optJSAI2016 opt) $ do
    let bs = Set.fromList [a | a <- range bnd, a `Map.notMember` m0, a `Map.notMember` viaPos]
    forM_ (range bnd) $ \a@(x,y,z) -> do
      let a_n = (x,y-1,z)
          a_s = (x,y+1,z)
          a_w = (x-1,y,z)
          a_e = (x+1,y,z)
          a_nw = Set.fromList $ takeWhile (inRange bnd) $ tail $ iterate (\(x,y,z) -> (x-1,y-1,z)) a
          a_ne = Set.fromList $ takeWhile (inRange bnd) $ tail $ iterate (\(x,y,z) -> (x+1,y-1,z)) a
          a_sw = Set.fromList $ takeWhile (inRange bnd) $ tail $ iterate (\(x,y,z) -> (x-1,y+1,z)) a
          a_se = Set.fromList $ takeWhile (inRange bnd) $ tail $ iterate (\(x,y,z) -> (x+1,y+1,z)) a
      when (inRange bnd a_n && inRange bnd a_w && a_nw `Set.isSubsetOf` bs) $ do
        SAT.addAtMost enc [evs Map.! (a_w,a), evs Map.! (a_n,a)] 1
      when (inRange bnd a_n && inRange bnd a_e && a_ne `Set.isSubsetOf` bs) $ do
        SAT.addAtMost enc [evs Map.! (a,a_e), evs Map.! (a_n,a)] 1
      when (inRange bnd a_s && inRange bnd a_w && a_sw `Set.isSubsetOf` bs) $ do
        SAT.addAtMost enc [evs Map.! (a_w,a), evs Map.! (a,a_s)] 1
      when (inRange bnd a_s && inRange bnd a_e && a_se `Set.isSubsetOf` bs) $ do
        SAT.addAtMost enc [evs Map.! (a,a_e), evs Map.! (a,a_s)] 1

  forM_ ls $ \(k, (_,_,z1), (_,_,z2)) -> do
    let vsk = [vs!k | (_, vs) <- Map.toList viaVs]
    if z1 == z2 then do
      -- ADC2016では(層をまたぐLINE数)=(VIA数)なので、他のLINEはVIAを使えない
      when (optADC2016 opt) $ SAT.addAtMost enc vsk 0
    else do
      -- 異なる盤面にある数字はビアを必ず使う
      SAT.addClause enc vsk
      -- ADC2016では(層をまたぐLINE数)=(VIA数)
      when (optADC2016 opt) $ SAT.addAtMost enc vsk 1

  return (vs, evs)

encodeObj :: SAT.AddPBLin m enc => enc -> Options -> Problem -> Encoded -> m SAT.PBLinSum
encodeObj enc opt Problem{ probSize = (w,h,d) } (cells,edges) = do
  let (o1, o2) = fromJust (optOptimize opt)
  obj1 <-
    if not o1 then do
      return []   
    else if optAssumeNoBlank opt then do
      v <- SAT.newVar enc
      SAT.addClause enc [v]
      return [(fromIntegral (w*h*d), v)]
    else
      return [(1, -(vs!0)) | vs <- elems cells]
  obj2 <-
    if not o2 then do
      return []
    else do
      forM (range (bounds cells)) $ \a@(x,y,z) -> do
        let w = ((x-1,y,z),a)
            e = (a,(x+1,y,z))
            n = ((x,y-1,z),a)
            s = (a,(x,y+1,z))
        v <- SAT.newVar enc
        forM_ [e,w] $ \e1 -> do
          case Map.lookup e1 edges of
            Nothing -> return ()
            Just v1 -> do
              forM_ [n,s] $ \e2 -> do
                case Map.lookup e2 edges of
                  Nothing -> return ()
                  Just v2 -> SAT.addClause enc [-v1, -v2, v]
        return (1,v)
  return $ obj1 ++ obj2

type Solution = (Map Cell Number, Set Edge)

decode :: Problem -> Encoded -> SAT.Model -> Solution
decode prob (vs, evs) m = (solCells, solEdges)
  where
    solCells = Map.fromList $ do
      a <- range (bounds vs)
      guard $ a `Set.member` usedCells
      case [k | (k,v) <- assocs (vs!a), SAT.evalLit m v] of
        k:_ -> return (a,k)
        [] -> mzero
    solEdges = Set.fromList [e | e@(a,_) <- edges, a `Set.member` usedCells]
    
    edges = [e | (e,ev) <- Map.toList evs, SAT.evalLit m ev]
    adjacents = Map.fromListWith Set.union $ concat $ [[(a, Set.singleton b), (b, Set.singleton a)] | (a,b) <- edges]
    usedVias = Set.fromList [(x,y,z) | ((x,y),zs) <- Map.toList cs, z <- [Set.findMin zs .. Set.findMax zs]]
      where
        cs = Map.fromList [((x,y), Set.singleton z) | (_,as) <- probVias prob, a@(x,y,z) <- as, a `Map.member` adjacents]
    usedCells = Set.union usedVias cs
      where
        cs = Set.unions [g (Set.fromList [a,b]) Set.empty | (_k,a,b) <- probLines prob]
        g xs visited
          | Set.null xs = visited
          | otherwise = g (Set.unions [Map.findWithDefault Set.empty x adjacents Set.\\ visited | x <- Set.toList xs]) (Set.union xs visited)

evalObj :: Options -> Problem -> Solution -> Integer
evalObj opt Problem{ probSize = (w,h,d) } (cells,edges) = obj1 + obj2
  where
    (o1, o2) = fromJust (optOptimize opt)
    bnd = ((0,0,1),(w-1,h-1,d))
    obj1
      | not o1 = 0
      | otherwise = fromIntegral $ Map.size cells
    obj2
      | not o2 = 0
      | otherwise = sum $ do
          a@(x,y,z) <- range bnd
          let w = ((x-1,y,z),a)
              e = (a,(x+1,y,z))
              n = ((x,y-1,z),a)
              s = (a,(x,y+1,z))
          if null [() | e1 <- [e,w], e1 `Set.member` edges, e2 <- [n,s], e2 `Set.member` edges] then
            return 0
          else
            return 1

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
  let (w,h,d) = probSize prob
  forM_ [1 .. d] $ \z -> do
    when (probIsMultiLayer prob) $ do
      unless (z == 1) $ putStrLn ""
      putStrLn $ "LAYER " ++ show z
    forM_ [0 .. h-1] $ \y -> do
      putStrLn $ concat $ intersperse ","
       [ case Map.lookup (x,y,z) cells of
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
  { optOptimize :: Maybe Obj
  , optAssumeNoBlank :: Bool
  , optAssumeNoDetour :: Bool
  , optJSAI2016 :: Bool
  , optADC2016 :: Bool
  , optNumSolutions :: Int
  }

instance Default Options where
  def =
    Options
    { optOptimize = Nothing
    , optAssumeNoBlank = False
    , optAssumeNoDetour = False
    , optJSAI2016 = False
    , optADC2016 = False
    , optNumSolutions = 1
    }

type Obj = (Bool,Bool)

options :: [OptDescr (Options -> Options)]
options =
    [ Option [] ["optimize"]
        (OptArg (\arg opt -> opt{ optOptimize = Just (maybe (True,True) readObj arg) }) "<str>")
        "Specify objective functions (-n option will be ignored): both (default), length, corners"
    , Option [] ["no-blank"]
        (NoArg (\opt -> opt{ optAssumeNoBlank = True }))
        "Assume no blank cells in solution"
    , Option [] ["no-detour"]
        (NoArg (\opt -> opt{ optAssumeNoDetour = True }))
        "Assume no detour in solution"
    , Option [] ["jsai2016"]
        (NoArg (\opt -> opt{ optJSAI2016 = True }))
        "Add constraints of JSATI2016 paper of Tatsuya Seko et.al."
    , Option [] ["adc2016"]
        (NoArg (\opt -> opt{ optADC2016 = True }))
        "Add constraints specific to ADC2016 rule"
    , Option ['n'] []
        (ReqArg (\val opt -> opt{ optNumSolutions = read val }) "<int>")
        "Maximal number of solutions to enumerate, or negative value for all solutions (default: 1)"
    ]
  where
    readObj = f . map toLower
      where
        f "both" = (True, True)
        f "length" = (True, False)
        f "corners" = (False, True)
        f _ = error "unknown objective"

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
            Right prob@Problem{ probSize = (w,h,d) } -> do
              putStrLn $ "SIZE " ++ show w ++ "X" ++ show h ++
                           (if probIsMultiLayer prob then "X" ++ show d else "")
              case optOptimize opt of
                Nothing -> do
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
                Just _ -> do
                  solver <- SAT.newSolver
                  SAT.setLogger solver $ hPutStrLn stderr
                  encoded@(cells,_edges) <- encode solver opt prob
                  unless (optAssumeNoBlank opt) $ do
                    forM_ (elems cells) $ \xs -> do
                      SAT.setVarPolarity solver (xs!0) False
                  obj <- encodeObj solver opt prob encoded
                  pbo <- PBO.newOptimizer2 solver obj (\m -> evalObj opt prob (decode prob encoded m))
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
              obj <- do
                encoded <- encode store opt prob
                case optOptimize opt of
                  Nothing -> return Nothing
                  Just _ -> do
                    obj <- encodeObj store opt prob encoded
                    return $ Just [(c,[v]) | (c,v) <- obj]
              opb <- PBStore.getPBFormula store
              FF.writeFile fname2 $ opb{ PB.pbObjectiveFunction = obj }
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
