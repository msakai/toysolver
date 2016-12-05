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
  | Insertion
  | QuickXplain
  deriving (Eq, Ord, Enum, Bounded, Show)

-- | Options for MUS finding.
--
-- The default value can be obtained by 'def'.
data Options
  = Options
  { optMethod     :: Method
  , optLogger     :: String -> IO ()
  , optShowLit    :: Lit -> String
  , optEvalConstr :: SAT.Model -> Lit -> Bool
    -- ^ Because each soft constraint /C_i/ is represented as a selector
    -- literal /l_i/ together with a hard constraint /l_i ⇒ C_i/, there
    -- are cases that a model assigns false to /l_i/ even though /C_i/
    -- itself is true. This function is used to inform the truth value
    -- of the original constraint /C_i/ that corresponds to the selector
    -- literal /l_i/.
  , optUpdateBest :: US -> IO ()
  }

instance Default Options where
  def =
    Options
    { optMethod     = Linear
    , optLogger     = \_ -> return ()
    , optShowLit    = show
    , optEvalConstr = SAT.evalLit
    , optUpdateBest = \_ -> return ()
    }
