-----------------------------------------------------------------------------
-- |
-- Module      :  pb2lp
-- Copyright   :  (c) Masahiro Sakai 2011-2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module Main where

import Control.Monad
import Data.Char
import Data.List
import Data.Maybe
import qualified Data.IntSet as IS
import qualified Data.Set as Set
import qualified Data.Map as Map
import System.Environment
import System.IO
import System.Exit
import System.Console.GetOpt
import qualified Text.PBFile as PBFile
import qualified Text.LPFile as LPFile

convert :: ObjType -> PBFile.Formula -> LPFile.LP
convert objType formula@(obj, cs) = LPFile.LP
  { LPFile.variables = vs2
  , LPFile.dir = dir
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

    (dir,obj2) =
      case obj of
        Just obj' -> (LPFile.OptMin, convExpr obj')
        Nothing ->
          case objType of
            ObjNone    -> (LPFile.OptMin, [LPFile.Term 0 (take 1 (Set.toList vs2 ++ ["x0"]))])
            ObjMaxOne  -> (LPFile.OptMax, [LPFile.Term 1 [v] | v <- Set.toList vs2])
            ObjMaxZero -> (LPFile.OptMin, [LPFile.Term 1 [v] | v <- Set.toList vs2])
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

convertWBO :: PBFile.SoftFormula -> Bool -> LPFile.LP
convertWBO formula@(top, cs) useIndicator = LPFile.LP
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
      let 
          lhs2 = convExpr lhs
          c = sum [c | LPFile.Term c [] <- lhs2]
          lhs3 = [t | t@(LPFile.Term c (_:_)) <- lhs2]
          rhs3 = fromIntegral rhs - c
          v = "r" ++ show n
          (ts,ind) =
            case w of
              Nothing -> ([], Nothing)
              Just w2 -> ([(w2, v)], Just (v,0))
      if isNothing w || useIndicator then do
         let op2 =
               case op of
                 PBFile.Ge -> LPFile.Ge
                 PBFile.Eq -> LPFile.Eql
         return (ts, (Nothing, ind, (lhs3, op2, rhs3)))
       else do
         let (lhsGE,rhsGE) = relaxGE v (lhs3,rhs3)
         case op of
           PBFile.Ge -> do
             return (ts, (Nothing, Nothing, (lhsGE, LPFile.Ge, rhsGE)))
           PBFile.Eq -> do
             let (lhsLE,rhsLE) = relaxLE v (lhs3,rhs3)
             [ (ts, (Nothing, Nothing, (lhsGE, LPFile.Ge, rhsGE)))
               , ([], (Nothing, Nothing, (lhsLE, LPFile.Le, rhsLE)))
               ]

relaxGE :: LPFile.Var -> (LPFile.Expr, Rational) -> (LPFile.Expr, Rational)
relaxGE v (lhs, rhs) = (LPFile.Term (rhs - lhs_lb) [v] : lhs, rhs)
  where
    lhs_lb = sum [min c 0 | LPFile.Term c _ <- lhs]

relaxLE :: LPFile.Var -> (LPFile.Expr, Rational) -> (LPFile.Expr, Rational)
relaxLE v (lhs, rhs) = (LPFile.Term (rhs - lhs_ub) [v] : lhs, rhs)
  where
    lhs_ub = sum [max c 0 | LPFile.Term c _ <- lhs]

collectVariablesWBO :: PBFile.SoftFormula -> IS.IntSet
collectVariablesWBO (top, cs) = IS.unions [f s | (_,(s,_,_)) <- cs]
  where
    f :: PBFile.Sum -> IS.IntSet
    f xs = IS.fromList $ do
      (_,ts) <- xs
      lit <- ts
      return $ abs lit

data Flag
  = Help
  | WBO
  | ObjType ObjType
  | IndicatorConstraint
  deriving Eq

data ObjType = ObjNone | ObjMaxOne | ObjMaxZero
  deriving Eq

options :: [OptDescr Flag]
options =
    [ Option ['h'] ["help"] (NoArg Help) "show help"
    , Option []    ["wbo"]  (NoArg WBO)  "input is .wbo file"
    , Option []    ["obj"]  (ReqArg (ObjType . parseObjType) "STRING") "objective function for PBS: none (default), max-one, max-zero"
    , Option []    ["indicator"] (NoArg IndicatorConstraint) "use indicator constraints in output LP file"
    ]
  where
    parseObjType s =
      case map toLower s of
        "none"     -> ObjNone
        "max-one"  -> ObjMaxOne
        "max-zero" -> ObjMaxZero
        _          -> error ("unknown obj: " ++ s)

main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    (o,_,[])
      | Help `elem` o -> putStrLn (usageInfo header options)
    (o,[fname],[]) -> do
      let objType = last (ObjNone : [t | ObjType t <- o])
      lp <-
        if WBO `elem` o
        then do
          ret <- if fname == "-"
                 then liftM (PBFile.parseWBOString "-") getContents
                 else PBFile.parseWBOFile fname
          case ret of
            Left err -> hPrint stderr err >> exitFailure
            Right formula -> return (convertWBO formula (IndicatorConstraint `elem` o))
        else do
          ret <- if fname == "-"
                 then liftM (PBFile.parseOPBString "-") getContents
                 else PBFile.parseOPBFile fname
          case ret of
            Left err -> hPrint stderr err >> exitFailure
            Right formula -> return (convert objType formula)
      case LPFile.render lp of
        Nothing -> hPutStrLn stderr "conversion failure" >> exitFailure
        Just s -> putStr s
    (o,_,errs) ->
      hPutStrLn stderr $ concat errs ++ usageInfo header options

header :: String
header = "Usage: pb2lp [--wbo] [file.opb|file.wbo|-]"