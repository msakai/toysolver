-----------------------------------------------------------------------------
-- |
-- Module      :  pb2lp
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module Main where

import Control.Monad
import Data.List
import qualified Data.IntSet as IS
import qualified Data.Set as Set
import qualified Data.Map as Map
import System.Environment
import System.IO
import System.Exit
import qualified PBFile
import qualified LPFile

header :: String
header = "Usage: pb2lp [--wbo] [file.opb|file.wbo|-]"

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
    vs2 = (Set.fromList . map convVar . IS.toList) $ vs1

    obj2 =
      case obj of
        Nothing -> [LPFile.Term 1 [v] | v <- Set.toList vs2]
        Just obj' -> convExpr obj'
    cs2 = do
      (lhs,op,rhs) <- cs
      let op2 = case op of
                  PBFile.Ge -> LPFile.Ge
                  PBFile.Eq -> LPFile.Eql
          lhs2 = convExpr lhs
          c = sum [c | LPFile.Term c [] <- lhs2]
          lhs3 = [t | t@(LPFile.Term c (_:_)) <- lhs2]
      return (Nothing, Nothing, (lhs3, op2, fromIntegral rhs - c))

convExpr :: PBFile.Sum -> LPFile.Expr
convExpr = concatMap g2
  where
    g2 :: PBFile.WeightedTerm -> LPFile.Expr
    g2 (w, tm) = foldl' prodE [LPFile.Term (fromIntegral w) []] (map g3 tm)

    g3 :: PBFile.Lit -> LPFile.Expr
    g3 x
      | x > 0     = [LPFile.Term 1 [convVar x]]
      | otherwise = [LPFile.Term 1 [], LPFile.Term (-1) [convVar (abs x)]]

    prodE :: LPFile.Expr -> LPFile.Expr -> LPFile.Expr
    prodE e1 e2 = [prodT t1 t2 | t1 <- e1, t2 <- e2]

    prodT :: LPFile.Term -> LPFile.Term -> LPFile.Term
    prodT (LPFile.Term c1 vs1) (LPFile.Term c2 vs2) = LPFile.Term (c1*c2) (vs1++vs2)

convVar :: PBFile.Var -> LPFile.Var
convVar x = ("x" ++ show x)

collectVariables :: PBFile.Formula -> IS.IntSet
collectVariables (obj, cs) = IS.unions $ maybe IS.empty f obj : [f s | (s,_,_) <- cs]
  where
    f :: PBFile.Sum -> IS.IntSet
    f xs = IS.fromList $ do
      (_,ts) <- xs
      lit <- ts
      return $ abs lit

convertWBO :: PBFile.SoftFormula -> LPFile.LP
convertWBO formula@(top, cs) = LPFile.LP
  { LPFile.variables = vs2
  , LPFile.dir = LPFile.OptMin
  , LPFile.objectiveFunction = (Nothing, obj2)
  , LPFile.constraints = map snd cs2
  , LPFile.bounds = Map.empty
  , LPFile.integerVariables = Set.empty
  , LPFile.binaryVariables = vs2
  , LPFile.semiContinuousVariables = Set.empty
  , LPFile.sos = []
  }
  where
    vs1 = collectVariablesWBO formula
    vs2 = ((Set.fromList . map convVar . IS.toList) $ vs1) `Set.union` vs3
    vs3 = Set.fromList [v | (ts, _) <- cs2, (_, v) <- ts]

    obj2 = [LPFile.Term (fromIntegral w) [v] | (ts, _) <- cs2, (w, v) <- ts]

    cs2 :: [([(Integer, LPFile.Var)], LPFile.Constraint)]
    cs2 = do
      (n, (w, (lhs,op,rhs))) <- zip [0..] cs
      let op2 = case op of
                  PBFile.Ge -> LPFile.Ge
                  PBFile.Eq -> LPFile.Eql
          lhs2 = convExpr lhs
          c = sum [c | LPFile.Term c [] <- lhs2]
          lhs3 = [t | t@(LPFile.Term c (_:_)) <- lhs2]
      let v = "r" ++ show n
          (ts,ind) =
            case w of
              Nothing -> ([], Nothing)
              Just w2 -> ([(w2, v)], Just (v,0))
      return (ts, (Nothing, ind, (lhs3, op2, fromIntegral rhs - c)))

collectVariablesWBO :: PBFile.SoftFormula -> IS.IntSet
collectVariablesWBO (top, cs) = IS.unions [f s | (_,(s,_,_)) <- cs]
  where
    f :: PBFile.Sum -> IS.IntSet
    f xs = IS.fromList $ do
      (_,ts) <- xs
      lit <- ts
      return $ abs lit



main :: IO ()
main = do
  args <- getArgs

  lp <-
    case args of
      "--wbo":args2 -> do
        ret <- case args2 of
               ["-"]   -> liftM (PBFile.parseWBOString "-") getContents
               [fname] -> PBFile.parseWBOFile fname
               _ -> hPutStrLn stderr header >> exitFailure
        case ret of
          Left err -> hPrint stderr err >> exitFailure
          Right formula -> return (convertWBO formula)      
      args2 -> do
        ret <- case args2 of
               ["-"]   -> liftM (PBFile.parseOPBString "-") getContents
               [fname] -> PBFile.parseOPBFile fname
               _ -> hPutStrLn stderr header >> exitFailure
        case ret of
          Left err -> hPrint stderr err >> exitFailure
          Right formula -> return (convert formula)

  case LPFile.render lp of
    Nothing -> hPutStrLn stderr "conversion failure" >> exitFailure
    Just s -> putStr s
