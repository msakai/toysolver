{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  SAT.PBO
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Pseudo-Boolean Optimization (PBO) Solver
--
-----------------------------------------------------------------------------
module SAT.PBO where

import Control.Monad
import Data.List
import Data.Ord
import Text.Printf
import SAT
import SAT.Types

data SearchStrategy
  = LinearSearch
  | BinarySearch
  -- | AdaptiveSearch

data Options
  = Options
  { optLogger               :: String -> IO ()
  , optUpdater              :: Model -> Integer -> IO ()
  , optObjFunVarsHeuristics :: Bool
  , optSearchStrategy       :: SearchStrategy
  }

defaultOptions :: Options
defaultOptions
  = Options
  { optLogger               = \_ -> return ()
  , optUpdater              = \_ _ -> return ()
  , optObjFunVarsHeuristics = True
  , optSearchStrategy       = LinearSearch
  }

minimize :: Solver -> [(Integer, Lit)] -> Options -> IO (Maybe Model)
minimize solver obj opt = do
  when (optObjFunVarsHeuristics opt) $ do
    forM_ obj $ \(c,l) -> do
      let p = if c > 0 then not (litPolarity l) else litPolarity l
      setVarPolarity solver (litVar l) p
    forM_ (zip [1..] (map snd (sortBy (comparing fst) [(abs c, l) | (c,l) <- obj]))) $ \(n,l) -> do
      replicateM n $ varBumpActivity solver (litVar l)

  result <- solve solver
  if not result then
     return Nothing
   else
     case optSearchStrategy opt of
       LinearSearch -> liftM Just linSearch
       BinarySearch -> liftM Just binSearch

  where
   logIO :: String -> IO ()
   logIO = optLogger opt

   update :: Model -> Integer -> IO ()
   update = optUpdater opt

   linSearch :: IO Model
   linSearch = do
     m <- model solver
     let v = pbEval m obj
     update m v
     addPBAtMost solver obj (v - 1)
     result <- solve solver
     if result
       then linSearch
       else return m

   binSearch :: IO Model
   binSearch = do
{-
     logIO $ printf "Binary Search: minimizing %s \n" $ 
       intercalate " "
         [c' ++ " " ++ l'
         | (c,l) <- obj
         , let c' = if c < 0 then show c else "+" ++ show c
         , let l' = (if l < 0 then "~" else "") ++ "x" ++ show (litVar l)
         ]
-}
     m0 <- model solver
     let v0 = pbEval m0 obj
     update m0 v0
     let ub0 = v0 - 1
         lb0 = pbLowerBound obj
     addPBAtMost solver obj ub0

     let loop lb ub m | ub < lb = return m
         loop lb ub m = do
           let mid = (lb + ub) `div` 2
           logIO $ printf "Binary Search: %d <= obj <= %d; guessing obj <= %d\n" lb ub mid
           sel <- newVar solver
           addPBAtMostSoft solver sel obj mid
           ret <- solveWith solver [sel]
           if ret
           then do
             m2 <- model solver
             let v = pbEval m2 obj
             update m2 v
             -- deactivating temporary constraint
             -- FIXME: 本来は制約の削除をしたい
             addClause solver [-sel]
             let ub' = v - 1
             logIO $ printf "Binary Search: updating upper bound: %d -> %d\n" ub ub'
             addPBAtMost solver obj ub'
             loop lb ub' m2
           else do
             -- deactivating temporary constraint
             -- FIXME: 本来は制約の削除をしたい
             addClause solver [-sel]
             let lb' = mid + 1
             logIO $ printf "Binary Search: updating lower bound: %d -> %d\n" lb lb'
             addPBAtLeast solver obj lb'
             loop lb' ub m

     loop lb0 ub0 m0
