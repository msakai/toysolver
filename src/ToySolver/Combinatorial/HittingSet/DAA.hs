{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
module ToySolver.Combinatorial.HittingSet.DAA
  ( Problem (..)
  , SimpleProblem (..)
  , Options (..)
  , run
  , generateCNFAndDNF
  ) where

import Control.Monad
import Control.Monad.Identity
import Data.Default.Class
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Set (Set)
import qualified Data.Set as Set
import qualified ToySolver.Combinatorial.HittingSet.Simple as HTC

class Monad m => Problem prob m | prob -> m where
  universe :: prob -> IntSet

  isInteresting :: prob -> IntSet -> m Bool

  maximalInterestingSet :: prob -> IntSet -> m (Maybe IntSet)
  maximalInterestingSet prob xs = do
   b <- isInteresting prob xs
   if not b then
     return Nothing
   else do
     let f ys z = do
           let ys' = IntSet.insert z ys
           b2 <- isInteresting prob ys'
           if b2 then return ys' else return ys
     liftM Just $ foldM f xs (IntSet.toList (universe prob `IntSet.difference` xs))

data SimpleProblem m = SimpleProblem IntSet (IntSet -> m Bool)

instance Monad m => Problem (SimpleProblem m) m where
  universe (SimpleProblem univ _) = univ
  isInteresting (SimpleProblem _ f) = f


data Options m
  = Options
  { optMinimalHittingSets :: Set IntSet -> Set IntSet
  , optOnMaxPosFound :: IntSet -> m ()
  , optOnMinNegFound :: IntSet -> m ()
  }

instance Monad m => Default (Options m) where
  def =
    Options
    { optMinimalHittingSets = HTC.minimalHittingSets
    , optOnMaxPosFound = \_ -> return ()
    , optOnMinNegFound = \_ -> return ()
    }

run :: forall prob m. Problem prob m => prob -> Options m -> m (Set IntSet, Set IntSet)
run prob opt = loop Set.empty Set.empty
  where
    univ :: IntSet
    univ = universe prob

    complement :: IntSet -> IntSet
    complement = (univ `IntSet.difference`)

    loop :: Set IntSet -> Set IntSet -> m (Set IntSet, Set IntSet)
    loop comp_pos neg = do
      let xss = optMinimalHittingSets opt comp_pos `Set.difference` neg
      if Set.null xss then
        return (Set.map complement comp_pos, neg)
      else do
        (comp_pos',neg') <- loop2 comp_pos neg (Set.toList xss)
        loop comp_pos' neg'

    loop2 :: Set IntSet -> Set IntSet -> [IntSet] -> m (Set IntSet, Set IntSet)
    loop2 comp_pos neg [] = return (comp_pos, neg)
    loop2 comp_pos neg (xs : xss) = do
      ret <- maximalInterestingSet prob xs
      case ret of
        Nothing -> do          
          optOnMinNegFound opt xs
          loop2 comp_pos (Set.insert xs neg) xss
        Just ys -> do
          optOnMaxPosFound opt ys
          return (Set.insert (complement ys) comp_pos, neg)

-- | Compute the irredundant CNF representation and DNF representation.
--
-- Let /f/ be a monotone boolean function over set of variables /S/.
-- This function returns /C/ and /D/ where ∧_{I∈C} ∨_{i∈I} x_i and
-- ∨_{I∈D} ∧_{i∈I} x_i are the irredundant CNF representation /f/ and
-- DNF representation of /f/ respectively.
generateCNFAndDNF
  :: IntSet -- ^ Set of variables /V/
  -> (IntSet -> Bool) -- ^ A monotone boolean function /f/ from /{0,1}^|V| ≅ P(V)/ to @Bool@
  -> (Set IntSet, Set IntSet)
generateCNFAndDNF vs f = (Set.map (vs `IntSet.difference`) pos, neg)
  where
    prob = SimpleProblem vs (return . not . f)
    (pos,neg) = runIdentity $ run prob def
