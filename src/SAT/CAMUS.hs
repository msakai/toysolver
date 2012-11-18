-----------------------------------------------------------------------------
-- |
-- Module      :  SAT.CAMUS
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module SAT.CAMUS
  ( MUS
  , MCS
  , Options (..)
  , defaultOptions
  , enumMCSes
  , allMCSes
  , allMUSes
  ) where

import Control.Monad
import Data.Array.IArray
import qualified Data.IntSet as IS
import Data.List
import Data.IORef
import SAT

type MUS = [Lit]
type MCS = [Lit]

-- | Options for 'enumMCSes' function
data Options
  = Options
  { optLogger   :: String -> IO ()
  , optCallback :: MCS -> IO ()
  }

-- | default 'Options' value
defaultOptions :: Options
defaultOptions =
  Options
  { optLogger     = \_ -> return ()
  , optCallback   = \_ -> return ()
  }

enumMCSes :: SAT.Solver -> [Lit] -> Options -> IO ()
enumMCSes solver sels opt = loop 1
  where
    log :: String -> IO ()
    log = optLogger opt

    callback :: MCS -> IO ()
    callback = optCallback opt

    loop k = do
      log $ "CAMUS: k = " ++ show k
      ret <- SAT.solve solver
      when ret $ do
        vk <- SAT.newVar solver
        SAT.addPBAtMostSoft solver vk [(1,-sel) | sel <- sels] k
        let loop2 = do
              ret2 <- SAT.solveWith solver [vk]
              when ret2 $ do
                m <- SAT.model solver
                let mcs = [sel | sel <- sels, not (evalLit sel m)]
                callback mcs
                SAT.addClause solver mcs
                loop2
        loop2
        SAT.addClause solver [-vk]
        loop (k+1)

evalLit :: Lit -> Model -> Bool
evalLit l m = m ! SAT.litVar l == SAT.litPolarity l

allMCSes :: SAT.Solver -> [Lit] -> IO [MCS]
allMCSes solver sels = do
  ref <- newIORef []  
  let opt =
        defaultOptions
        { optCallback = \mcs -> modifyIORef ref (mcs:)
        }
  enumMCSes solver sels opt
  readIORef ref

-- FIXME: nub
allMUSes :: [MCS] -> [MUS]
allMUSes mcses = nub $ f (map IS.fromList mcses) []
  where
    f :: [IS.IntSet] -> [Int] -> [MUS]
    f [] mus = return mus
    f mcses mus = do
      sel <- IS.toList $ IS.unions mcses
      let mus' = sel:mus
      mcs <- mcses
      guard $ sel `IS.member` mcs
      let mcses' = propagateChoice mcses sel mcs
      f mcses' mus'

propagateChoice :: [IS.IntSet] -> Lit -> IS.IntSet -> [IS.IntSet]
propagateChoice mcses sel mcs = zs
  where
    xs = filter (sel `IS.notMember`) mcses
    ys = map (IS.filter (sel <) . (`IS.difference` mcs)) xs
    zs = maintainNoSupersets ys

maintainNoSupersets :: [IS.IntSet] -> [IS.IntSet]
maintainNoSupersets xss = go [] xss
  where
    go yss [] = yss
    go yss (xs:xss) = go (xs : filter p yss) (filter p xss)
      where
        p zs = not (xs `IS.isSubsetOf` zs)
