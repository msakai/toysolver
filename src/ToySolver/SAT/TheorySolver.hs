module ToySolver.SAT.TheorySolver
  ( TheorySolver (..)
  , emptyTheory
  ) where

import ToySolver.SAT.Types

data TheorySolver =
  TheorySolver
  { thAssertLit :: (Lit -> IO Bool) -> Lit -> IO Bool
  , thCheck     :: (Lit -> IO Bool) -> IO Bool
  , thExplain   :: IO [Lit]
  , thPushBacktrackPoint :: IO ()
  , thPopBacktrackPoint  :: IO ()
  }

emptyTheory :: TheorySolver
emptyTheory =
  TheorySolver
  { thAssertLit = \propagate lit -> return True
  , thCheck = \propagate -> return True
  , thExplain = error "should not happen"
  , thPushBacktrackPoint = return ()
  , thPopBacktrackPoint  = return ()
  }
