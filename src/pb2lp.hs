module Main where

import Control.Monad
import qualified Data.Set as Set
import qualified Data.Map as Map
import System.Environment
import System.IO
import System.Exit
import qualified PBFile
import qualified LPFile

header :: String
header = "Usage: pb2lp2 [file.opb|-]"

convert :: PBFile.Formula -> LPFile.LP
convert formula@(obj, cs) = LPFile.LP
  { LPFile.variables = vs2
  , LPFile.dir = LPFile.OptMin
  , LPFile.objectiveFunction = (Nothing, obj2)
  , LPFile.constraints = cs2
  , LPFile.bounds = Map.empty
  , LPFile.integerVariables = Set.empty
  , LPFile.binaryVariables = vs2
  , LPFile.semiContinuousVariables = Set.empty
  , LPFile.sos = []
  }
  where
    vs1 = collectVariables formula
    vs2 = Set.map h vs1

    obj2 =
      case obj of
        Nothing -> [LPFile.Term 1 [v] | v <- Set.toList vs2]
        Just obj' -> g obj'
    cs2 = do
      (lhs,op,rhs) <- cs
      let op2 = case op of
                  PBFile.Ge -> LPFile.Ge
                  PBFile.Eq -> LPFile.Eql
      return (Nothing, Nothing, (g lhs, op2, fromIntegral rhs))

    g :: PBFile.Sum -> LPFile.Expr
    g = concatMap g2
      where
        g2 :: PBFile.WeightedTerm -> LPFile.Expr
        g2 (w, tm) = [LPFile.Term (fromIntegral w * c) vs  | LPFile.Term c vs <- concatMap g3 tm]

        g3 :: PBFile.Lit -> LPFile.Expr
        g3 (PBFile.Pos x) = [LPFile.Term 1 [h x]]
        g3 (PBFile.Neg x) = [LPFile.Term 1 [], LPFile.Term (-1) [h x]]

        prodE :: LPFile.Expr -> LPFile.Expr -> LPFile.Expr
        prodE e1 e2 = [prodT t1 t2 | t1 <- e1, t2 <- e2]

        prodT :: LPFile.Term -> LPFile.Term -> LPFile.Term
        prodT (LPFile.Term c1 vs1) (LPFile.Term c2 vs2) = LPFile.Term (c1*c2) (vs1++vs2)

    h :: PBFile.Var -> LPFile.Var
    h x = ("x" ++ show x)

collectVariables :: PBFile.Formula -> Set.Set PBFile.Var
collectVariables (obj, cs) = Set.unions $ maybe Set.empty f obj : [f s | (s,_,_) <- cs]
  where
    f :: PBFile.Sum -> Set.Set PBFile.Var
    f xs = Set.fromList $ do
      (_,ts) <- xs
      lit <- ts
      case lit of
        PBFile.Pos v -> return v
        PBFile.Neg v -> return v

main :: IO ()
main = do
  args <- getArgs
  ret <- case args of
         ["-"]   -> liftM (PBFile.parseOPBString "-") getContents
         [fname] -> PBFile.parseOPBFile fname
         _ -> hPutStrLn stderr header >> exitFailure
  case ret of
    Left err -> hPrint stderr err >> exitFailure
    Right formula ->
      case LPFile.render (convert formula) of
        Nothing -> hPutStrLn stderr "conversion failure" >> exitFailure
        Just s -> putStr s
