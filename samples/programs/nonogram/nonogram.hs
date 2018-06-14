{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, CPP #-}
{-# OPTIONS_GHC -Wall #-}
module Main where

import Control.Applicative
import Control.Monad
import Data.Array.IArray
import Data.Array.Unboxed
import Data.IORef
import Data.List (group)
import Data.Map (Map)
import qualified Data.Map as Map
import System.Console.GetOpt
import System.Environment
import System.Exit
import System.IO
import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import ToySolver.Internal.Util (setEncodingChar8)

-- row patterns and column patterns
type Problem = ([[Int]], [[Int]])

type Solution = UArray (Int,Int) Bool

readCWDFile :: FilePath -> IO Problem
readCWDFile fname = withFile fname ReadMode hReadCWD

hReadCWD :: Handle -> IO Problem
hReadCWD h = do
  nrows <- read <$> hGetLine h
  ncols <- read <$> hGetLine h
  (rows::[[Int]]) <- replicateM nrows $ liftM (filter (/=0) . map read . words) $ hGetLine h
  _ <- hGetLine h -- empty line
  (cols::[[Int]]) <- replicateM ncols $ liftM (filter (/=0) . map read . words) $ hGetLine h
  unless (length rows == nrows) $ error "row number mismatch"
  unless (length cols == ncols) $ error "column number mismatch"
  return (rows, cols)

checkSolution :: Problem -> Solution -> IO ()
checkSolution (rows, cols) sol = do
  let nrows = length rows
      ncols = length cols  
  forM_ [0..nrows-1] $ \i -> do
    let row_i_expected = rows !! i
        row_i_actual = [length g | g <- group [sol ! (i,j) | j <- [0..ncols-1]], head g]
    unless (row_i_expected == row_i_actual) $ error (show row_i_expected ++ " /= " ++ show row_i_actual)
  forM_ [0..ncols-1] $ \j -> do
    let col_j_expected = cols !! j
        col_j_actual = [length g | g <- group [sol ! (i,j) | i <- [0..nrows-1]], head g]
    unless (col_j_expected == col_j_actual) $ error (show col_j_expected ++ " /= " ++ show col_j_actual)

hPrintSolution :: Handle -> Solution -> Char -> Char -> IO ()
hPrintSolution h sol cell0 cell1 = do
  let ((r0,c0),(rn,cn)) = bounds sol
  forM_ [r0..rn] $ \i -> do
    hPutStrLn h [if sol ! (i,j) then cell1 else cell0 | j <- [c0..cn]]

solve :: Problem -> IO (IO (Maybe Solution))
solve (rows, cols) = do
  let nrows = length rows
      ncols = length cols
  solver <- SAT.newSolver
  enc <- Tseitin.newEncoder solver

  bTrue  <- Tseitin.encodeConj enc []
  bFalse <- Tseitin.encodeDisj enc []
          
  (bs :: UArray (Int,Int) SAT.Lit) <- liftM (array ((0,0),(nrows-1,ncols-1)) . concat) $ forM [0..nrows-1] $ \i -> do
    forM [0..ncols-1] $ \j -> do
      b <- SAT.newVar solver
      return ((i,j),b)

  forM_ (zip [0..] rows) $ \(i, xs) -> do         
    ref <- newIORef Map.empty
    let f j []
          | j >= ncols = return bTrue
          | otherwise = do
              m <- readIORef ref
              case Map.lookup (j,[]) m of
                Just b -> return b
                Nothing -> do
                  b' <- f (j+1) []                  
                  b <- Tseitin.encodeConj enc [- (bs ! (i,j)), b']
                  writeIORef ref (Map.insert (j,[]) b m)
                  return b
        f j ns@(_ : _) | j + sum ns + length ns - 1 > ncols = return bFalse
        f j (n : ns) = do
          m <- readIORef ref
          case Map.lookup (j, n:ns) m of
            Just b -> return b
            Nothing -> do
              b1 <- do
                b1' <- f (j+1) (n : ns)
                Tseitin.encodeConj enc [- (bs ! (i,j)), b1']
              b2 <- do
                b2' <- f (j+n+1) ns
                Tseitin.encodeConj enc $ [bs ! (i,j') | j' <- [j..j+n-1]] ++ [- (bs ! (i,j+n)) | j+n < ncols] ++ [b2']
              b <- Tseitin.encodeDisj enc [b1,b2]
              writeIORef ref (Map.insert (j,n:ns) b m)
              return b
    b <- f 0 xs
    SAT.addClause solver [b]

  forM_ (zip [0..] cols) $ \(j, xs) -> do
    ref <- newIORef Map.empty
    let f i []
          | i >= nrows = return bTrue
          | otherwise = do
              m <- readIORef ref
              case Map.lookup (i,[]) m of
                Just b -> return b
                Nothing -> do
                  b' <- f (i+1) []
                  b <- Tseitin.encodeConj enc [- (bs ! (i,j)), b']
                  writeIORef ref (Map.insert (i,[]) b m)
                  return b
        f i ns@(_ : _) | i + sum ns + length ns - 1 > nrows = return bFalse
        f i (n : ns) = do
          m <- readIORef ref
          case Map.lookup (i, n:ns) m of
            Just b -> return b
            Nothing -> do
              b1 <- do
                b1' <- f (i+1) (n : ns)
                Tseitin.encodeConj enc [- (bs ! (i,j)), b1']
              b2 <- do
                b2' <- f (i+n+1) ns
                Tseitin.encodeConj enc $ [bs ! (i',j) | i' <- [i..i+n-1]] ++ [- (bs ! (i+n,j)) | i+n < nrows] ++ [b2']
              b <- Tseitin.encodeDisj enc [b1,b2]
              writeIORef ref (Map.insert (i,n:ns) b m)
              return b
    b <- f 0 xs
    SAT.addClause solver [b]

  return $ do
    ret <- SAT.solve solver
    if not ret then
      return Nothing
    else do
      m <- SAT.getModel solver
      SAT.addClause solver [if val then -var else var | (var,val) <- assocs m]
      let sol = amap (SAT.evalLit m) bs
      return (Just sol)

data Options
  = Options
  { optHelp   :: Bool
  , optSolLim :: Int
  }

defaultOptions :: Options
defaultOptions =
  Options
  { optHelp   = False
  , optSolLim = 1
  }

options :: [OptDescr (Options -> Options)]
options =
    [ Option ['h'] ["help"]   (NoArg (\opt -> opt{ optHelp = True })) "show help"
    , Option ['n'] []
        (ReqArg (\val opt -> opt{ optSolLim = read val }) "<int>")
        "maximum number of solutions to enumerate, or -1 to enumerate all solutions (default: 1)"
    ]

showHelp :: Handle -> IO ()
showHelp h = hPutStrLn h (usageInfo header options)
  where
    header = "Usage: nonogram [OPTIONS] FILE"

main :: IO ()
main = do
#ifdef FORCE_CHAR8
  setEncodingChar8
#endif

  args <- getArgs
  case getOpt Permute options args of
    (_,_,errs@(_:_)) -> do
      mapM_ putStrLn errs
      exitFailure
    (o,args2,[]) -> do
      let opt = foldl (flip id) defaultOptions o
      when (optHelp opt) $ do
        showHelp stdout
        exitSuccess
      case args2 of
        [] -> do
          showHelp stderr
          exitFailure
        fname : _ -> do
          prob <- readCWDFile fname
          act <- solve prob
          let loop n | optSolLim opt >= 0, n >= optSolLim opt = do
                hPutStrLn stderr $ "reached to solution enumeration limit " ++ show n
              loop n = do
                m <- act
                case m of
                  Nothing -> do
                    hPutStrLn stderr $ "enumerated all of " ++ show n ++ " solutions"
                  Just sol -> do
                    checkSolution prob sol
                    when (n > 0) $ hPutStrLn stdout ""
                    hPrintSolution stdout sol '.' '#'
                    hFlush stdout
                    loop (n+1)
          loop (0::Int)
