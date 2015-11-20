module ToySolver.SAT.TheorySolver
  ( TheorySolver (..)
  , emptyTheory
  ) where

import ToySolver.SAT.Types

data TheorySolver =
  TheorySolver
  { thAssertLit :: (Lit -> IO Bool) -> Lit -> IO Bool
  , thCheck     :: (Lit -> IO Bool) -> IO Bool
  , thExplain   :: Maybe Lit -> IO [Lit]
  , thPushBacktrackPoint :: IO ()
  , thPopBacktrackPoint  :: IO ()
  , thConstructModel :: IO ()
  }

emptyTheory :: TheorySolver
emptyTheory =
  TheorySolver
  { thAssertLit = \propagate lit -> return True
  , thCheck = \propagate -> return True
  , thExplain = \_ -> error "should not happen"
  , thPushBacktrackPoint = return ()
  , thPopBacktrackPoint  = return ()
  , thConstructModel = return ()
  }
