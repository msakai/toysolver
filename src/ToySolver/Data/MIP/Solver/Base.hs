{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FunctionalDependencies #-}
module ToySolver.Data.MIP.Solver.Base
  ( SolveOptions (..)
  , Default (..)
  , IsSolver (..)
  ) where

import Data.Default.Class
import Data.Scientific (Scientific)
import ToySolver.Data.MIP.Base as MIP

data SolveOptions
  = SolveOptions
  { solveTimeLimit :: Maybe Double
    -- ^ time limit in seconds
  }

instance Default SolveOptions where
  def =
    SolveOptions
    { solveTimeLimit = Nothing
    }

class Monad m => IsSolver s m | s -> m where
  solve :: s -> SolveOptions -> MIP.Problem Scientific -> m (MIP.Solution Scientific)
