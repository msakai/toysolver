{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wall #-}
import Control.Monad
import qualified Data.Foldable as F
import Data.Char
import Data.Default.Class
import Data.List.Split
import Data.Maybe
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Data.Text.Lazy.IO as TLIO
import ToySolver.Data.MIP ((.==.), (.>=.))
import qualified ToySolver.Data.MIP as MIP
import System.Console.GetOpt
import System.Environment
import System.Exit
import System.IO
import ToySolver.Internal.Util (setEncodingChar8)

type Problem = [(Int, IntMap Double)]

-- http://ntucsu.csie.ntu.edu.tw/~cjlin/libsvmtools/datasets/
loadFile :: FilePath -> IO Problem
loadFile fname = do
  s <- readFile fname
  return $ map f (lines s)
  where
    f :: String -> (Int, IntMap Double)
    f s =
      case words s of
        (y : xs) -> (read (dropWhile ('+'==) y), IntMap.fromList [(read v, read val) | x <- xs, let [v,val] = splitOn ":" x])

primal :: Maybe Double -> Problem -> MIP.Problem
primal c prob
  = def
  { MIP.objectiveFunction = def
      { MIP.objDir = MIP.OptMin
      , MIP.objExpr =
         sum [MIP.constExpr (1/2) * wj * wj | wj <- fmap MIP.varExpr $ IntMap.elems w] +
         sum [MIP.constExpr (realToFrac (fromJust c)) * xi_i | isJust c, xi_i <- fmap MIP.varExpr xi]
      }
  , MIP.constraints =
      [ MIP.constExpr (fromIntegral y_i) * (IntMap.map MIP.varExpr w `dot` IntMap.map (MIP.constExpr . realToFrac) xs_i - MIP.varExpr b)
        .>=. 1 - (if isJust c then MIP.varExpr xi_i else 0)
      | ((y_i, xs_i), xi_i) <- zip prob xi
      ]
  , MIP.varType = Map.fromList [(x, MIP.ContinuousVariable) | x <- b : [w_j | w_j <- IntMap.elems w] ++ [xi_i | isJust c, xi_i <- xi]]
  , MIP.varBounds =
      Map.unions
      [ Map.singleton b (MIP.NegInf, MIP.PosInf)
      , Map.fromList [(w_j, (MIP.NegInf, MIP.PosInf)) | w_j <- IntMap.elems w]
      , Map.fromList [(xi_i, (0, MIP.PosInf)) | isJust c, xi_i <- xi]
      ]
  }
  where
    m = length prob
    n = fst $ IntMap.findMax $ IntMap.unions (map snd prob)
    w = IntMap.fromList [(j, MIP.toVar ("w_" ++ show j)) | j <- [1..n]]
    b = MIP.toVar "b"
    xi = [MIP.toVar ("xi_" ++ show i) | i <- [1..m]]

dual
  :: Maybe Double
  -> (IntMap Double -> IntMap Double -> Double)
  -> Problem
  -> MIP.Problem
dual c kernel prob
  = def
  { MIP.objectiveFunction = def
      { MIP.objDir = MIP.OptMax
      , MIP.objExpr = MIP.Expr $
          [MIP.Term 1 [a_i] | a_i <- a] ++
          [ MIP.Term (- (1/2) * fromIntegral (y_i * y_j) * realToFrac (kernel xs_i xs_j)) [a_i, a_j]
          | ((y_i, xs_i), a_i) <- zip prob a
          , ((y_j, xs_j), a_j) <- zip prob a
          ]
      }
  , MIP.constraints =
      [ MIP.Expr [ MIP.Term (fromIntegral y_i) [a_i] | ((y_i, _xs_i), a_i) <- zip prob a ] .==. 0 ]
  , MIP.varType = Map.fromList [(a_i, MIP.ContinuousVariable) | a_i <- a]
  , MIP.varBounds = Map.fromList [(a_i, (0, if isJust c then MIP.Finite (realToFrac (fromJust c)) else MIP.PosInf)) | a_i <- a]
  }
  where
    m = length prob
    a = [MIP.toVar ("a_" ++ show i) | i <- [1..m]]

dot :: Num a => IntMap a -> IntMap a -> a
dot a b = sum $ IntMap.elems $ IntMap.intersectionWith (*) a b

gaussian :: Double -> IntMap Double -> IntMap Double -> Double
gaussian sigma a b
  = exp (- F.sum (IntMap.map (**2) (IntMap.unionWith (+) a (IntMap.map negate b))) / (2 * sigma**2))

data Options
  = Options
  { optHelp          :: Bool
  , optDual          :: Bool
  , optKernel        :: String
  , optC             :: Maybe Double
  , optGamma         :: Maybe Double
  }

defaultOptions :: Options
defaultOptions =
  Options
  { optHelp          = False
  , optDual          = False
  , optKernel        = "linear"
  , optC             = Nothing
  , optGamma         = Nothing
  }

options :: [OptDescr (Options -> Options)]
options =
    [ Option ['h'] ["help"]   (NoArg (\opt -> opt{ optHelp = True })) "show help"
    , Option [] ["primal"]
        (NoArg (\opt -> opt{ optDual = False }))
        "Use primal form."
    , Option [] ["dual"]
        (NoArg (\opt -> opt{ optDual = True } ))
        "Use dual form."
    , Option [] ["kernel"]
        (ReqArg (\val opt -> opt{ optKernel = val }) "<str>")
        "Kernel: linear (default), gaussian"
    , Option ['c'] []
        (ReqArg (\val opt -> opt{ optC = Just $! read val }) "<float>")
        "C parameter"
    , Option [] ["gamma"]
        (ReqArg (\val opt -> opt{ optGamma = Just $! read val }) "<float>")
        "gamma parameter used for gaussian kernel"
    ]

showHelp :: Handle -> IO ()
showHelp h = hPutStrLn h (usageInfo header options)
  where
    header = "Usage: svm2lp [OPTIONS] FILE"

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
          svm <- loadFile fname
          let mip =
               case map toLower (optKernel opt) of
                 "linear" -> do
                   if optDual opt
                   then dual (optC opt) dot svm
                   else primal (optC opt) svm
                 "gaussian" -> do
                   case optGamma opt of
                     Nothing -> error "--gamma= must be specified"
                     Just gamma -> dual (optC opt) (gaussian gamma) svm
                 _ -> error $ "unknown kernel: "  ++ optKernel opt
          case MIP.toLPString def mip of
            Left err -> do
              hPutStrLn stderr err
              exitFailure
            Right s -> do
              TLIO.putStr s
