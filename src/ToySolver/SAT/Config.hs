module ToySolver.SAT.Config
  ( -- * Solver configulation
    Config (..)
  , RestartStrategy (..)
  , showRestartStrategy
  , parseRestartStrategy
  , LearningStrategy (..)
  , showLearningStrategy
  , parseLearningStrategy
  , BranchingStrategy (..)
  , showBranchingStrategy
  , parseBranchingStrategy
  , PBHandlerType (..)
  , showPBHandlerType
  , parsePBHandlerType
  , configParser
  ) where

import Control.Applicative
import Data.Char
import Data.Default.Class
import Data.List
import Data.Monoid
import Options.Applicative

data Config
  = Config
  { configRestartStrategy :: !RestartStrategy
  , configRestartFirst :: !Int
    -- ^ The initial restart limit. (default 100)
    -- Zero and negative values are used to disable restart.
  , configRestartInc :: !Double
    -- ^ The factor with which the restart limit is multiplied in each restart. (default 1.5)
    -- This must be @>1@.
  , configLearningStrategy :: !LearningStrategy
  , configLearntSizeFirst :: !Int
    -- ^ The initial limit for learnt constraints.
    -- Negative value means computing default value from problem instance.
  , configLearntSizeInc :: !Double
    -- ^ The limit for learnt constraints is multiplied with this factor periodically. (default 1.1)
    -- This must be @>1@.                     
  , configCCMin :: !Int
    -- ^ Controls conflict constraint minimization (0=none, 1=local, 2=recursive)
  , configBranchingStrategy :: !BranchingStrategy
  , configERWAStepSizeFirst :: !Double
    -- ^ step-size α in ERWA and LRB branching heuristic is initialized with this value. (default 0.4)
  , configERWAStepSizeDec :: !Double
    -- ^ step-size α in ERWA and LRB branching heuristic is decreased by this value after each conflict. (default 0.06)
  , configERWAStepSizeMin :: !Double
    -- ^ step-size α in ERWA and LRB branching heuristic is decreased until it reach the value. (default 0.06)
  , configEMADecay :: !Double
    -- ^ inverse of the variable EMA decay factor used by LRB branching heuristic. (default 1 / 0.95)
  , configEnablePhaseSaving :: !Bool
  , configEnableForwardSubsumptionRemoval :: !Bool
  , configEnableBackwardSubsumptionRemoval :: !Bool
  , configRandomFreq :: !Double
    -- ^ The frequency with which the decision heuristic tries to choose a random variable
  , configPBHandlerType :: !PBHandlerType
  , configEnablePBSplitClausePart :: !Bool
    -- ^ Split PB-constraints into a PB part and a clause part.
    --
    -- Example from minisat+ paper:
    --
    -- * 4 x1 + 4 x2 + 4 x3 + 4 x4 + 2y1 + y2 + y3 ≥ 4
    -- 
    -- would be split into
    --
    -- * x1 + x2 + x3 + x4 + ¬z ≥ 1 (clause part)
    --
    -- * 2 y1 + y2 + y3 + 4 z ≥ 4 (PB part)
    --
    -- where z is a newly introduced variable, not present in any other constraint.
    -- 
    -- Reference:
    -- 
    -- * N . Eéen and N. Sörensson. Translating Pseudo-Boolean Constraints into SAT. JSAT 2:1–26, 2006.
    --                               
  , configCheckModel :: !Bool
  , configVarDecay :: !Double
    -- ^ Inverse of the variable activity decay factor. (default 1 / 0.95)
  , configConstrDecay :: !Double
    -- ^ Inverse of the constraint activity decay factor. (1 / 0.999)
  } deriving (Show, Eq, Ord)

instance Default Config where
  def =
    Config
    { configRestartStrategy = def
    , configRestartFirst = 100
    , configRestartInc = 1.5
    , configLearningStrategy = def
    , configLearntSizeFirst = -1
    , configLearntSizeInc = 1.1
    , configCCMin = 2
    , configBranchingStrategy = def
    , configERWAStepSizeFirst = 0.4
    , configERWAStepSizeDec = 10**(-6)
    , configERWAStepSizeMin = 0.06
    , configEMADecay = 1 / 0.95
    , configEnablePhaseSaving = True
    , configEnableForwardSubsumptionRemoval = False
    , configEnableBackwardSubsumptionRemoval = False
    , configRandomFreq = 0.005
    , configPBHandlerType = def
    , configEnablePBSplitClausePart = False
    , configCheckModel = False
    , configVarDecay = 1 / 0.95
    , configConstrDecay = 1 / 0.999
    }

-- | Restart strategy.
--
-- The default value can be obtained by 'def'.
data RestartStrategy = MiniSATRestarts | ArminRestarts | LubyRestarts
  deriving (Show, Eq, Ord, Enum, Bounded)

instance Default RestartStrategy where
  def = MiniSATRestarts

showRestartStrategy :: RestartStrategy -> String
showRestartStrategy MiniSATRestarts = "minisat"
showRestartStrategy ArminRestarts = "armin"
showRestartStrategy LubyRestarts = "luby"

parseRestartStrategy :: String -> Maybe RestartStrategy
parseRestartStrategy s =
  case map toLower s of
    "minisat" -> Just MiniSATRestarts
    "armin" -> Just ArminRestarts
    "luby" -> Just LubyRestarts
    _ -> Nothing

-- | Learning strategy.
--
-- The default value can be obtained by 'def'.
data LearningStrategy
  = LearningClause
  | LearningHybrid
  deriving (Show, Eq, Ord, Enum, Bounded)

instance Default LearningStrategy where
  def = LearningClause

showLearningStrategy :: LearningStrategy -> String
showLearningStrategy LearningClause = "clause"
showLearningStrategy LearningHybrid = "hybrid"

parseLearningStrategy :: String -> Maybe LearningStrategy
parseLearningStrategy s =
  case map toLower s of
    "clause" -> Just LearningClause
    "hybrid" -> Just LearningHybrid
    _ -> Nothing

-- | Branching strategy.
--
-- The default value can be obtained by 'def'.
--
-- 'BranchingERWA' and 'BranchingLRB' is based on [Liang et al 2016].
--
-- * J. Liang, V. Ganesh, P. Poupart, and K. Czarnecki, "Learning rate based branching heuristic for SAT solvers,"
--   in Proceedings of Theory and Applications of Satisfiability Testing (SAT 2016), pp. 123-140.
--   <http://link.springer.com/chapter/10.1007/978-3-319-40970-2_9>
--   <https://cs.uwaterloo.ca/~ppoupart/publications/sat/learning-rate-branching-heuristic-SAT.pdf>
data BranchingStrategy
  = BranchingVSIDS
    -- ^ VSIDS (Variable State Independent Decaying Sum) branching heuristic
  | BranchingERWA
    -- ^ ERWA (Exponential Recency Weighted Average) branching heuristic
  | BranchingLRB
    -- ^ LRB (Learning Rate Branching) heuristic
  deriving (Show, Eq, Ord, Enum, Bounded)

instance Default BranchingStrategy where
  def = BranchingVSIDS

showBranchingStrategy :: BranchingStrategy -> String
showBranchingStrategy BranchingVSIDS = "vsids"
showBranchingStrategy BranchingERWA  = "erwa"
showBranchingStrategy BranchingLRB   = "lrb"

parseBranchingStrategy :: String -> Maybe BranchingStrategy
parseBranchingStrategy s =
  case map toLower s of
    "vsids" -> Just BranchingVSIDS
    "erwa"  -> Just BranchingERWA
    "lrb"   -> Just BranchingLRB
    _ -> Nothing

-- | Pseudo boolean constraint handler implimentation.
--
-- The default value can be obtained by 'def'.
data PBHandlerType = PBHandlerTypeCounter | PBHandlerTypePueblo
  deriving (Show, Eq, Ord, Enum, Bounded)

instance Default PBHandlerType where
  def = PBHandlerTypeCounter

showPBHandlerType :: PBHandlerType -> String
showPBHandlerType PBHandlerTypeCounter = "counter"
showPBHandlerType PBHandlerTypePueblo = "pueblo"

parsePBHandlerType :: String -> Maybe PBHandlerType
parsePBHandlerType s =
  case map toLower s of
    "counter" -> Just PBHandlerTypeCounter
    "pueblo" -> Just PBHandlerTypePueblo
    _ -> Nothing

configParser :: Parser Config
configParser = Config
  <$> restartOption
  <*> restartFirstOption
  <*> restartIncOption
  <*> learningOption
  <*> learntSizeFirstOption
  <*> learntSizeIncOption
  <*> ccMinOption
  <*> branchOption
  <*> eRWAStepSizeFirstOption
  <*> eRWAStepSizeDecOption
  <*> eRWAStepSizeMinOption
  <*> eMADecayOption
  <*> enablePhaseSavingOption
  <*> enableForwardSubsumptionRemovalOption
  <*> enableBackwardSubsumptionRemovalOption
  <*> randomFreqOption
  <*> pbHandlerTypeOption
  <*> enablePBSplitClausePartOption
  <*> checkModelOption
  <*> pure (configVarDecay def)
  <*> pure (configConstrDecay def)
  where
    restartOption = option (maybeReader parseRestartStrategy)
      $  long "restart"
      <> metavar "STR"
      <> help ("Restart startegy: " ++ intercalate ", " [showRestartStrategy s | s <- [minBound..maxBound]])
      <> value (configRestartStrategy def)
      <> showDefaultWith showRestartStrategy
    restartFirstOption = option auto
      $  long "restart-first"
      <> metavar "INT"
      <> help "The initial restart limit."
      <> value (configRestartFirst def)
      <> showDefault
    restartIncOption = option auto
      $  long "restart-inc"
      <> metavar "REAL"
      <> help "The factor with which the restart limit is multiplied in each restart."
      <> value (configRestartInc def)
      <> showDefault

    learningOption = option (maybeReader parseLearningStrategy)
      $  long "learning"
      <> metavar "STR"
      <> help ("Leaning scheme: " ++ intercalate ", " [showLearningStrategy s | s <- [minBound..maxBound]])
      <> value (configLearningStrategy def)
      <> showDefaultWith showLearningStrategy
    learntSizeFirstOption = option auto
      $  long "learnt-size-first"
      <> metavar "INT"
      <> help "The initial limit for learnt clauses."
      <> value (configLearntSizeFirst def)
      <> showDefault
    learntSizeIncOption = option auto
      $  long "learnt-size-inc"
      <> metavar "REAL"
      <> help "The limit for learnt clauses is multiplied with this factor periodically."
      <> value (configLearntSizeInc def)
      <> showDefault

    ccMinOption = option auto
      $  long "ccmin"
      <> metavar "INT"
      <> help "Conflict clause minimization: 0=none, 1=local, 2=recursive"
      <> value (configCCMin def)
      <> showDefault
    branchOption = option (maybeReader parseBranchingStrategy)
      $  long "branch"
      <> metavar "STR"
      <> help ("Branching startegy: " ++ intercalate ", " [showBranchingStrategy s | s <- [minBound..maxBound]])
      <> value (configBranchingStrategy def)
      <> showDefaultWith showBranchingStrategy

    eRWAStepSizeFirstOption = option auto
      $  long "erwa-alpha-first"
      <> metavar "REAL"
      <> help "step-size alpha in ERWA and LRB branching heuristic is initialized with this value."
      <> value (configERWAStepSizeFirst def)
      <> showDefault
    eRWAStepSizeDecOption = option auto
      $  long "erwa-alpha-dec"
      <> metavar "REAL"
      <> help "step-size alpha in ERWA and LRB branching heuristic is decreased by this value after each conflict."
      <> value (configERWAStepSizeDec def)
      <> showDefault
    eRWAStepSizeMinOption = option auto
      $  long "erwa-alpha-min"
      <> metavar "REAL"
      <> help "step-size alpha in ERWA and LRB branching heuristic is decreased until it reach the value."
      <> value (configERWAStepSizeMin def)
      <> showDefault

    eMADecayOption = option auto
      $  long "ema-decay"
      <> metavar "REAL"
      <> help "inverse of the variable EMA decay factor used by LRB branching heuristic."
      <> value (configEMADecay def)
      <> showDefault

    enablePhaseSavingOption =
          flag' True  (long "enable-phase-saving"  <> help ("Enable phase saving"  ++ (if configEnablePhaseSaving def then " (default)" else "")))
      <|> flag' False (long "disable-phase-saving" <> help ("Disable phase saving" ++ (if configEnablePhaseSaving def then "" else " (default)")))
      <|> pure (configEnablePhaseSaving def)

    enableForwardSubsumptionRemovalOption =
          flag' True
            (  long "enable-forward-subsumption-removal"
            <> help ("Enable forward subumption removal (clauses only)"  ++ (if configEnableForwardSubsumptionRemoval def then " (default)" else "")))
      <|> flag' False
            (  long "disable-forward-subsumption-removal"
            <> help ("Disable forward subumption removal (clauses only)" ++ (if configEnableForwardSubsumptionRemoval def then "" else " (default)")))
      <|> pure (configEnableForwardSubsumptionRemoval def)
    enableBackwardSubsumptionRemovalOption =
          flag' True
            (  long "enable-backward-subsumption-removal"
            <> help ("Enable backward subumption removal (clauses only)"  ++ (if configEnableBackwardSubsumptionRemoval def then " (default)" else "")))
      <|> flag' False
            (  long "disable-backward-subsumption-removal"
            <> help ("Disable backward subumption removal (clauses only)" ++ (if configEnableBackwardSubsumptionRemoval def then "" else " (default)")))
      <|> pure (configEnableBackwardSubsumptionRemoval def)

    randomFreqOption = option auto
      $  long "random-freq"
      <> metavar "0..1"
      <> help "The frequency with which the decision heuristic tries to choose a random variable"
      <> value (configRandomFreq def)
      <> showDefault

    pbHandlerTypeOption = option (maybeReader parsePBHandlerType)
      $  long "pb-handler"
      <> metavar "STR"
      <> help ("PB constraint handler: " ++ intercalate ", " [showPBHandlerType h | h <- [minBound..maxBound]])
      <> value (configPBHandlerType def)
      <> showDefaultWith showPBHandlerType

    enablePBSplitClausePartOption =
          flag' True
            (  long "pb-split-clause-part"
            <> help ("Split clause part of PB constraints." ++ (if configEnablePBSplitClausePart def then " (default)" else "")))
      <|> flag' False
            (  long "no-pb-split-clause-part"
            <> help ("Do not split clause part of PB constraints." ++ (if configEnablePBSplitClausePart def then "" else " (default)")))
      <|> pure (configEnablePBSplitClausePart def)

    checkModelOption = switch
      $  long "check-model"
      <> help "check model for debugging"

