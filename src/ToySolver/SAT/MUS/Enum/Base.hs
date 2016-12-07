module ToySolver.SAT.MUS.Enum.Base
  ( module ToySolver.SAT.MUS.Types
  , Method (..)
  , Options (..)
  ) where

import Data.Default.Class
import qualified ToySolver.SAT as SAT
import ToySolver.SAT.Types
import ToySolver.SAT.MUS.Types

data Method
  = CAMUS
  | DAA
  | MARCO
  deriving (Eq, Ord, Enum, Bounded, Show)

-- The default value can be obtained by 'def'.
data Options
  = Options
  { optMethod     :: Method
  , optLogger     :: String -> IO ()
  , optShowLit    :: Lit -> String
    -- ^ MCS candidates (see HYCAM paper for details).
    -- A MCS candidate must be a superset of a real MCS.
  , optEvalConstr :: SAT.Model -> Lit -> Bool
    -- ^ Because each soft constraint /C_i/ is represented as a selector
    -- literal /l_i/ together with a hard constraint /l_i ⇒ C_i/, there
    -- are cases that a model assigns false to /l_i/ even though /C_i/
    -- itself is true. This function is used to inform the truth value
    -- of the original constraint /C_i/ that corresponds to the selector
    -- literal /l_i/.
  , optOnMCSFound :: MCS -> IO ()
  , optOnMUSFound :: MUS -> IO ()
  , optKnownMCSes :: [MCS]
  , optKnownMUSes :: [MUS]
  , optKnownCSes  :: [CS]
  }

instance Default Options where
  def =
    Options
    { optMethod     = CAMUS
    , optLogger     = \_ -> return ()
    , optShowLit    = show
    , optEvalConstr = SAT.evalLit
    , optOnMCSFound = \_ -> return ()
    , optOnMUSFound = \_ -> return ()
    , optKnownMCSes = []
    , optKnownMUSes = []
    , optKnownCSes = []
    }
