-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.MUS.CAMUS
-- Copyright   :  (c) Masahiro Sakai 2012-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- In this module, we assume each soft constraint /C_i/ is represented as a literal.
-- If a constraint /C_i/ is not a literal, we can represent it as a fresh variable /v/
-- together with a hard constraint /v ⇒ C_i/.
--
-- References:
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
module ToySolver.SAT.MUS.CAMUS
  ( module ToySolver.SAT.MUS.Types
  , Options (..)
  , defaultOptions
  , allMCSAssumptions
  , allMUSAssumptions
  , enumMCSAssumptions
  , camus
  ) where

import Control.Monad
import Data.Array.IArray
import Data.Default.Class
import qualified Data.IntSet as IS
import Data.List
import Data.IORef
import qualified ToySolver.Combinatorial.HittingSet.Simple as HittingSet
import qualified ToySolver.SAT as SAT
import ToySolver.SAT.Types
import ToySolver.SAT.MUS.Types

-- | Options for 'enumMCSAssumptions', 'allMCSAssumptions', 'allMUSAssumptions'
data Options
  = Options
  { optLogger     :: String -> IO ()
  , optOnMCSFound :: MCS -> IO ()
  , optOnMUSFound :: MUS -> IO ()
  , optKnownMCSes :: [MCS]
  , optKnownMUSes :: [MUS]
  , optKnownCSes  :: [CS]
    -- ^ MCS candidates (see HYCAM paper for details).
    -- A MCS candidate must be a superset of a real MCS.
  }

instance Default Options where
  def = defaultOptions

-- | default 'Options' value
defaultOptions :: Options
defaultOptions =
  Options
  { optLogger     = \_ -> return ()
  , optOnMCSFound = \_ -> return ()
  , optOnMUSFound = \_ -> return ()
  , optKnownMCSes = []
  , optKnownMUSes = []
  , optKnownCSes = []
  }

enumMCSAssumptions :: SAT.Solver -> [Lit] -> Options -> IO ()
enumMCSAssumptions solver sels opt = do
  candRef <- newIORef [(IS.size cs, cs) | cs <- optKnownCSes opt]
  loop candRef 1

  where
    log :: String -> IO ()
    log = optLogger opt

    mcsFound :: MCS -> IO ()
    mcsFound mcs = do
      optOnMCSFound opt mcs
      SAT.addClause solver (IS.toList mcs)

    loop :: IORef [(Int, LitSet)] -> Int -> IO ()
    loop candRef k = do
      log $ "CAMUS: k = " ++ show k
      cand <- readIORef candRef

      ret <- if not (null cand) then return True else SAT.solve solver
      when ret $ do
        forM_ cand $ \(size,cs) -> do
          when (size == k) $ do
            -- If a candidate MCS is not superset of already obtained MCS,
            -- we are sure that it is actually an MCS.
            mcsFound cs
        writeIORef candRef [(size,cs) | (size,cs) <- cand, size /= k]

        vk <- SAT.newVar solver
        SAT.addPBAtMostSoft solver vk [(1,-sel) | sel <- sels] (fromIntegral k)
        let loop2 = do
              ret2 <- SAT.solveWith solver [vk]
              when ret2 $ do
                m <- SAT.getModel solver
                let mcs = IS.fromList [sel | sel <- sels, not (evalLit m sel)]
                mcsFound mcs
                modifyIORef candRef (filter (\(_,cs) -> not (mcs `IS.isSubsetOf` cs)))
                loop2
        loop2
        SAT.addClause solver [-vk]
        loop candRef (k+1)

allMCSAssumptions :: SAT.Solver -> [Lit] -> Options -> IO [MCS]
allMCSAssumptions solver sels opt = do
  ref <- newIORef []  
  let opt2 =
        opt
        { optOnMCSFound = \mcs -> do
            modifyIORef ref (mcs:)
            optOnMCSFound opt mcs
        }
  enumMCSAssumptions solver sels opt2
  readIORef ref

allMUSAssumptions :: SAT.Solver -> [Lit] -> Options -> IO [MUS]
allMUSAssumptions solver sels opt = do
  (muses, _mcses) <- camus solver sels opt
  return $ muses

camus :: SAT.Solver -> [Lit] -> Options -> IO ([MUS], [MCS])
camus solver sels opt = do
  log "CAMUS: MCS enumeration begins"
  mcses <- allMCSAssumptions solver sels opt
  log "CAMUS: MCS enumeration done"
  let muses = HittingSet.minimalHittingSets mcses
  mapM_ (optOnMUSFound opt) muses
  return (muses, mcses)
  where
    log :: String -> IO ()
    log = optLogger opt
