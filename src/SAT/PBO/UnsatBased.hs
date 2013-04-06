{-# LANGUAGE BangPatterns, DoAndIfThenElse #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  SAT.PBO.UnsatBased
-- Copyright   :  (c) Masahiro Sakai 2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module SAT.PBO.UnsatBased
  ( Options (..)
  , defaultOptions
  , solve
  , solveWBO
  ) where

import Control.Monad
import qualified Data.IntMap as IM
import qualified SAT as SAT
import qualified SAT.Types as SAT

data Options
  = Options
  { optLogger     :: String -> IO ()
  , optUpdateBest :: SAT.Model -> Integer -> IO ()
  , optUpdateLB   :: Integer -> IO ()
  }

defaultOptions :: Options
defaultOptions
  = Options
  { optLogger     = \_ -> return ()
  , optUpdateBest = \_ _ -> return ()
  , optUpdateLB   = \_ -> return ()
  }

solve :: SAT.Solver -> [(Integer, SAT.Lit)] -> Options -> IO (Maybe SAT.Model)
solve solver obj opt = do
  result <- solveWBO solver [(-v, c) | (c,v) <- obj'] opt'
  case result of
    Nothing -> return Nothing
    Just (m,_) -> return (Just m)
  where
    (obj',offset) = SAT.normalizePBSum (obj,0)
    opt' =
      opt
      { optUpdateBest = \m val -> optUpdateBest opt m (offset + val)
      , optUpdateLB   = \val -> optUpdateLB opt (offset + val)
      }

solveWBO :: SAT.Solver -> [(SAT.Lit, Integer)] -> Options -> IO (Maybe (SAT.Model, Integer))
solveWBO solver sels0 opt = loop 0 (IM.fromList sels0)
  where
    loop :: Integer -> IM.IntMap Integer -> IO (Maybe (SAT.Model, Integer))
    loop !lb sels = do
      optUpdateLB opt lb

      ret <- SAT.solveWith solver (IM.keys sels)
      if ret
      then do
        m <- SAT.model solver
        -- 余計な変数を除去する?
        optUpdateBest opt m lb
        return $ Just (m, lb)
      else do
        core <- SAT.failedAssumptions solver
        case core of
          [] -> return Nothing
          _  -> do
            let !min_c = minimum [sels IM.! sel | sel <- core]
                !lb' = lb + min_c

            xs <- forM core $ \sel -> do
              r <- SAT.newVar solver
              return (sel, r)
            SAT.addAtMost solver (map snd xs) 1

            ys <- liftM IM.unions $ forM xs $ \(sel, r) -> do
              s <- SAT.newVar solver
              SAT.addClause solver [-s, r, sel]
              let c = sels IM.! sel
              if c > min_c
                then return $ IM.fromList [(s, min_c), (sel, c - min_c)]
                else return $ IM.singleton s min_c
            let sels' = IM.union ys (IM.difference sels (IM.fromList [(sel, ()) | sel <- core]))

            loop lb' sels'
