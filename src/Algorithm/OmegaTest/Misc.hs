{-# OPTIONS_GHC -Wall #-}
module Algorithm.OmegaTest.Misc
  ( checkRealByCAD
  , checkRealBySimplex
  ) where

import Control.Monad
import qualified Data.IntMap as IM
import Data.Maybe
import System.IO.Unsafe

import Data.Expr
import qualified Data.LA as LA
import qualified Data.Polynomial as P
import qualified Algorithm.CAD as CAD
import qualified Algorithm.Simplex2 as Simplex2

checkRealByCAD :: [Var] -> [LA.Atom Rational] -> Bool
checkRealByCAD _ as = isJust $ CAD.solve (map (fmap f) as)
  where
    f :: LA.Expr Rational -> P.Polynomial Rational Int
    f t = P.fromTerms [(c, g x) | (c,x) <- LA.terms t]

    g :: Int -> P.MonicMonomial Int
    g x
      | x == LA.unitVar = P.mmOne
      | otherwise       = P.mmVar x

checkRealBySimplex :: [Var] -> [LA.Atom Rational] -> Bool
checkRealBySimplex vs as = unsafePerformIO $ do
  solver <- Simplex2.newSolver
  s <- liftM IM.fromList $ forM vs $ \v -> do
    v2 <- Simplex2.newVar solver
    return (v, LA.var v2)
  forM_ as $ \a -> do
    Simplex2.assertAtomEx solver (fmap (LA.applySubst s) a)
  Simplex2.check solver
