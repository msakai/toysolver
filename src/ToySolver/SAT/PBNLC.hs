{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ExistentialQuantification, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.PBNLC
-- Copyright   :  (c) Masahiro Sakai 2015
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ExistentialQuantification, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses)
-- 
-----------------------------------------------------------------------------
module ToySolver.SAT.PBNLC
  (
    PBTerm
  , PBSum
  , Encoder
  , newEncoder
  , getTseitinEncoder

  -- * Adding constraints
  , addPBNLAtLeast
  , addPBNLAtMost  
  , addPBNLExactly
  , addPBNLAtLeastSoft
  , addPBNLAtMostSoft
  , addPBNLExactlySoft

  -- * Linearlization
  , linearizePBSum
  , linearizePBSumWithPolarity

  -- * Evaluation
  , evalPBSum
  ) where

import Control.Monad.Primitive
import ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.TseitinEncoder as Tseitin
import ToySolver.Internal.Util (revForM)

type PBTerm = (Integer, [Lit])
type PBSum = [PBTerm]

data Encoder m
  = forall a. SAT.AddPBLin m a => Encoder
  { encBase    :: a
  , encTseitin :: Tseitin.Encoder m
  }

instance Monad m => SAT.NewVar m (Encoder m) where
  newVar Encoder{ encBase = a }   = SAT.newVar a
  newVars Encoder{ encBase = a }  = SAT.newVars a
  newVars_ Encoder{ encBase = a } = SAT.newVars_ a

instance Monad m => SAT.AddClause m (Encoder m) where
  addClause Encoder{ encBase = a } = SAT.addClause a

instance Monad m => SAT.AddCardinality m (Encoder m) where
  addAtLeast Encoder{ encBase = a } = SAT.addAtLeast a
  addAtMost  Encoder{ encBase = a } = SAT.addAtMost a
  addExactly Encoder{ encBase = a } = SAT.addExactly a

instance Monad m => SAT.AddPBLin m (Encoder m) where
  addPBAtLeast Encoder{ encBase = a } = SAT.addPBAtLeast a
  addPBAtMost  Encoder{ encBase = a } = SAT.addPBAtMost a
  addPBExactly Encoder{ encBase = a } = SAT.addPBExactly a
  addPBAtLeastSoft Encoder{ encBase = a } = SAT.addPBAtLeastSoft a
  addPBAtMostSoft  Encoder{ encBase = a } = SAT.addPBAtMostSoft a
  addPBExactlySoft Encoder{ encBase = a } = SAT.addPBExactlySoft a

newEncoder :: (Monad m, SAT.AddPBLin m a) => a -> Tseitin.Encoder m -> m (Encoder m)
newEncoder a tseitin = return $ Encoder a tseitin

getTseitinEncoder :: Encoder m -> Tseitin.Encoder m
getTseitinEncoder Encoder{ encTseitin = tseitin } = tseitin

-- | Add a non-linear pseudo boolean constraints /c1*ls1 + c2*ls2 + … ≥ n/.
addPBNLAtLeast
  :: PrimMonad m
  => Encoder m
  -> PBSum   -- ^ @[(c1,ls1),(c2,ls2),…]@
  -> Integer -- ^ /n/
  -> m ()
addPBNLAtLeast enc lhs rhs = do
  let c = sum [c | (c,[]) <- lhs]
  lhs' <- linearizePBSumWithPolarity enc Tseitin.polarityPos [(c,ls) | (c,ls) <- lhs, not (null ls)]
  SAT.addPBAtLeast enc lhs' (rhs - c)

-- | Add a non-linear pseudo boolean constraints /c1*ls1 + c2*ls2 + … ≥ n/.
addPBNLAtMost
  :: PrimMonad m
  => Encoder m
  -> PBSum   -- ^ @[(c1,ls1),(c2,ls2),…]@
  -> Integer -- ^ /n/
  -> m ()
addPBNLAtMost enc lhs rhs =
  addPBNLAtLeast enc [(-c,ls) | (c,ls) <- lhs] (negate rhs)

-- | Add a non-linear pseudo boolean constraints /c1*ls1 + c2*ls2 + … = n/.
addPBNLExactly
  :: PrimMonad m
  => Encoder m
  -> PBSum   -- ^ @[(c1,ls1),(c2,ls2),…]@
  -> Integer -- ^ /n/
  -> m ()
addPBNLExactly enc lhs rhs = do
  let c = sum [c | (c,[]) <- lhs]
  lhs' <- linearizePBSum enc [(c,ls) | (c,ls) <- lhs, not (null ls)]
  SAT.addPBExactly enc lhs' (rhs - c)

-- | Add a soft non-linear pseudo boolean constraints /sel ⇒ c1*ls1 + c2*ls2 + … ≥ n/.
addPBNLAtLeastSoft
  :: PrimMonad m
  => Encoder m
  -> Lit     -- ^ Selector literal @sel@
  -> PBSum   -- ^ @[(c1,ls1),(c2,ls2),…]@
  -> Integer -- ^ /n/
  -> m ()
addPBNLAtLeastSoft enc sel lhs rhs = do
  let c = sum [c | (c,[]) <- lhs]
  lhs' <- linearizePBSumWithPolarity enc Tseitin.polarityPos [(c,ls) | (c,ls) <- lhs, not (null ls)]
  SAT.addPBAtLeastSoft enc sel lhs' (rhs - c)

-- | Add a soft non-linear pseudo boolean constraints /sel ⇒ c1*ls1 + c2*ls2 + … ≤ n/.
addPBNLAtMostSoft
  :: PrimMonad m
  => Encoder m
  -> Lit     -- ^ Selector literal @sel@
  -> PBSum   -- ^ @[(c1,ls1),(c2,ls2),…]@
  -> Integer -- ^ /n/
  -> m ()
addPBNLAtMostSoft enc sel lhs rhs =
  addPBNLAtLeastSoft enc sel [(negate c, lit) | (c,lit) <- lhs] (negate rhs)

-- | Add a soft non-linear pseudo boolean constraints /lit ⇒ c1*ls1 + c2*ls2 + … = n/.
addPBNLExactlySoft
  :: PrimMonad m
  => Encoder m
  -> Lit     -- ^ indicator @lit@
  -> PBSum   -- ^ @[(c1,ls1),(c2,ls2),…]@
  -> Integer -- ^ /n/
  -> m ()
addPBNLExactlySoft enc sel lhs rhs = do
  let c = sum [c | (c,[]) <- lhs]
  lhs' <- linearizePBSum enc [(c,ls) | (c,ls) <- lhs, not (null ls)]
  SAT.addPBExactlySoft enc sel lhs' (rhs - c)

-- | Encode a non-linear 'PBSum' into a lienar 'PBLinSum'.
--
-- @linearizePBSum enc s@ is equivalent to @linearizePBSumWithPolarity enc polarityBoth@.
linearizePBSum
  :: PrimMonad m
  => Encoder m
  -> PBSum
  -> m PBLinSum
linearizePBSum enc = linearizePBSumWithPolarity enc Tseitin.polarityBoth

-- | Linearize a non-linear 'PBSum' into a lienar 'PBLinSum'.
--
-- The input 'PBSum' is assumed to occur only in specified polarity.
--
-- * If @'polarityPosOccurs' p@, the value of resulting 'PBLinSum' is /greater than/ or /equal to/ the value of original 'PBSum'.
--
-- * If @'polarityNegOccurs' p@, the value of resulting 'PBLinSum' is /lesser than/ or /equal to/ the value of original 'PBSum'.
-- 
linearizePBSumWithPolarity
  :: PrimMonad m
  => Encoder m
  -> Tseitin.Polarity -- polarity /p/
  -> PBSum
  -> m PBLinSum
linearizePBSumWithPolarity Encoder{ encTseitin = tseitin } p xs =
  revForM xs $ \(c,ls) -> do
    l <- if c > 0 then
           Tseitin.encodeConjWithPolarity tseitin p ls
         else
           Tseitin.encodeConjWithPolarity tseitin (Tseitin.negatePolarity p) ls
    return (c,l)

evalPBSum :: IModel m => m -> PBSum -> Integer
evalPBSum m xs = sum [c | (c,lits) <- xs, all (evalLit m) lits]
