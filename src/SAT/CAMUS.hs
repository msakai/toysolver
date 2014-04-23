-----------------------------------------------------------------------------
-- |
-- Module      :  SAT.CAMUS
-- Copyright   :  (c) Masahiro Sakai 2012-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- * [CAMUS] M. Liffiton and K. Sakallah, Algorithms for computing minimal
--   unsatisfiable subsets of constraints, Journal of Automated Reasoning,
--   vol. 40, no. 1, pp. 1-33, Jan. 2008. 
--   <http://sun.iwu.edu/~mliffito/publications/jar_liffiton_CAMUS.pdf>
--
-- * [HYCAM] A. Gregoire, B. Mazure, and C. Piette, Boosting a complete
--   technique to find MSS and MUS: thanks to a local search oracle, in
--   Proceedings of the 20th international joint conference on Artifical
--   intelligence, ser. IJCAI'07. San Francisco, CA, USA: Morgan Kaufmann
--   Publishers Inc., 2007, pp. 2300-2305.
--   <http://ijcai.org/papers07/Papers/IJCAI07-370.pdf>
--
-----------------------------------------------------------------------------
module SAT.CAMUS
  ( MUS
  , MCS
  , Options (..)
  , defaultOptions
  , allMCSAssumptions
  , allMUSAssumptions
  , enumMCSAssumptions
  , hittingSetDual
  ) where

import Control.Monad
import Data.Array.IArray
import qualified Data.IntSet as IS
import Data.List
import Data.IORef
import SAT
import SAT.Types

-- | Minimal Unsatisfiable Subset of constraints.
type MUS = [Lit]

-- | Minimal Correction Subset of constraints.
type MCS = [Lit]

-- | Options for 'enumMCSAssumptions', 'allMCSAssumptions', 'allMUSAssumptions'
data Options
  = Options
  { optLogger     :: String -> IO ()
  , optCallback   :: MCS -> IO ()
  , optMCSCandidates :: [MCS]
    -- ^ MCS candidates (see HYCAM paper for details).
    -- A MCS candidate must be a superset of real MCS.
  }

-- | default 'Options' value
defaultOptions :: Options
defaultOptions =
  Options
  { optLogger     = \_ -> return ()
  , optCallback   = \_ -> return ()
  , optMCSCandidates = []
  }

enumMCSAssumptions :: SAT.Solver -> [Lit] -> Options -> IO ()
enumMCSAssumptions solver sels opt = do
  candRef <- newIORef [(IS.size s, s) | mcs <- optMCSCandidates opt, let s = IS.fromList mcs]
  loop candRef 1

  where
    log :: String -> IO ()
    log = optLogger opt

    mcsFound :: MCS -> IO ()
    mcsFound mcs = do
      optCallback opt mcs
      SAT.addClause solver mcs

    loop :: IORef [(Int, LitSet)] -> Int -> IO ()
    loop candRef k = do
      log $ "CAMUS: k = " ++ show k
      cand <- readIORef candRef

      ret <- if not (null cand) then return True else SAT.solve solver
      when ret $ do
        forM_ cand $ \(size,cs) -> do
          when (size == k) $ do
            -- If a candidate MCS is not superset of already obtained MCS,
            -- we are sure that they are real MCS.
            mcsFound (IS.toList cs)
        writeIORef candRef [(size,cs) | (size,cs) <- cand, size /= k]

        vk <- SAT.newVar solver
        SAT.addPBAtMostSoft solver vk [(1,-sel) | sel <- sels] (fromIntegral k)
        let loop2 = do
              ret2 <- SAT.solveWith solver [vk]
              when ret2 $ do
                m <- SAT.model solver
                let mcs = [sel | sel <- sels, not (evalLit m sel)]
                    mcs' = IS.fromList mcs
                mcsFound mcs
                modifyIORef candRef (filter (\(_,cs) -> not (mcs' `IS.isSubsetOf` cs)))
                loop2
        loop2
        SAT.addClause solver [-vk]
        loop candRef (k+1)

allMCSAssumptions :: SAT.Solver -> [Lit] -> Options -> IO [MCS]
allMCSAssumptions solver sels opt = do
  ref <- newIORef []  
  let opt2 =
        opt
        { optCallback = \mcs -> do
            modifyIORef ref (mcs:)
            optCallback opt mcs
        }
  enumMCSAssumptions solver sels opt2
  readIORef ref

allMUSAssumptions :: SAT.Solver -> [Lit] -> Options -> IO [MCS]
allMUSAssumptions solver sels opt = do
  log "CAMUS: MCS enumeration begins"
  mcses <- allMCSAssumptions solver sels opt
  log "CAMUS: MCS enumeration done"
  return $ hittingSetDual mcses
  where
    log :: String -> IO ()
    log = optLogger opt

-- FIXME: remove nub
hittingSetDual :: [MCS] -> [MUS]
hittingSetDual mcses = nub $ f (map IS.fromList mcses) []
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
