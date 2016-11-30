-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.MUS.Base
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
--
-----------------------------------------------------------------------------
module ToySolver.SAT.MUS.Base
  ( module ToySolver.SAT.MUS.Types
  , Method (..)
  , Options (..)
  ) where

import Control.Monad
import Data.Default.Class
import Data.List
import qualified Data.IntSet as IS
import qualified ToySolver.SAT as SAT
import ToySolver.SAT.Types
import ToySolver.SAT.MUS.Types

data Method
  = Linear
  | QuickXplain
  deriving (Eq, Ord, Enum, Bounded, Show)

-- | Options for MUS finding.
--
-- The default value can be obtained by 'def'.
data Options
  = Options
  { optMethod     :: Method
  , optLogger     :: String -> IO ()
  , optUpdateBest :: [Lit] -> IO ()
  , optLitPrinter :: Lit -> String
  }

instance Default Options where
  def =
    Options
    { optMethod     = Linear
    , optLogger     = \_ -> return ()
    , optUpdateBest = \_ -> return ()
    , optLitPrinter = show
    }
