{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, ExistentialQuantification #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.TseitinEncoder
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, ExistentialQuantification)
-- 
-- Tseitin encoding
--
-- TODO:
-- 
-- * reduce variables.
--
-- References:
--
-- * [Tse83] G. Tseitin. On the complexity of derivation in propositional
--   calculus. Automation of Reasoning: Classical Papers in Computational
--   Logic, 2:466-483, 1983. Springer-Verlag. 
--
-- * [For60] R. Fortet. Application de l'algèbre de Boole en rechercheop
--   opérationelle. Revue Française de Recherche Opérationelle, 4:17-26,
--   1960. 
--
-- * [BM84a] E. Balas and J. B. Mazzola. Nonlinear 0-1 programming:
--   I. Linearization techniques. Mathematical Programming, 30(1):1-21,
--   1984.
-- 
-- * [BM84b] E. Balas and J. B. Mazzola. Nonlinear 0-1 programming:
--   II. Dominance relations and algorithms. Mathematical Programming,
--   30(1):22-45, 1984.
--
-- * [PG86] D. Plaisted and S. Greenbaum. A Structure-preserving
--    Clause Form Translation. In Journal on Symbolic Computation,
--    volume 2, 1986.
--
-- * [ES06] N . Eéen and N. Sörensson. Translating Pseudo-Boolean
--   Constraints into SAT. JSAT 2:1–26, 2006.
--
-----------------------------------------------------------------------------
module ToySolver.SAT.TseitinEncoder
  (
  -- * The @Encoder@ type
    Encoder
  , newEncoder
  , newEncoderWithPBLin
  , setUsePB

  -- * Polarity
  , Polarity (..)
  , negatePolarity
  , polarityPos
  , polarityNeg
  , polarityBoth
  , polarityNone

  -- * Boolean formula type
  , Formula
  , evalFormula

  -- * Encoding of boolean formulas
  , addFormula
  , encodeFormula
  , encodeFormulaWithPolarity
  , encodeConj
  , encodeConjWithPolarity
  , encodeDisj
  , encodeDisjWithPolarity
  , encodeITE
  , encodeITEWithPolarity

  -- * Retrieving definitions
  , getDefinitions
  ) where

import Control.Monad
import Control.Monad.Primitive
import Data.Primitive.MutVar
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.IntSet as IntSet
import ToySolver.Data.Boolean
import ToySolver.Data.BoolExpr
import qualified ToySolver.SAT.Types as SAT

-- | Arbitrary formula not restricted to CNF
type Formula = BoolExpr SAT.Lit

evalFormula :: SAT.IModel m => m -> Formula -> Bool
evalFormula m = fold (SAT.evalLit m)

-- | Encoder instance
data Encoder m =
  forall a. SAT.AddClause m a =>
  Encoder
  { encSolver    :: a
  , encAddPBAtLeast :: Maybe (SAT.PBLinSum -> Integer -> m ())
  , encUsePB     :: MutVar (PrimState m) Bool
  , encConjTable :: !(MutVar (PrimState m) (Map SAT.LitSet (SAT.Lit, Bool, Bool)))
  , encITETable  :: !(MutVar (PrimState m) (Map (SAT.Lit, SAT.Lit, SAT.Lit) (SAT.Lit, Bool, Bool)))
  }

instance Monad m => SAT.NewVar m (Encoder m) where
  newVar   Encoder{ encSolver = a } = SAT.newVar a
  newVars  Encoder{ encSolver = a } = SAT.newVars a
  newVars_ Encoder{ encSolver = a } = SAT.newVars_ a

instance Monad m => SAT.AddClause m (Encoder m) where
  addClause Encoder{ encSolver = a } = SAT.addClause a

-- | Create a @Encoder@ instance.
-- If the encoder is built using this function, 'setUsePB' has no effect.
newEncoder :: PrimMonad m => SAT.AddClause m a => a -> m (Encoder m)
newEncoder solver = do
  usePBRef <- newMutVar False
  table <- newMutVar Map.empty
  table2 <- newMutVar Map.empty
  return $
    Encoder
    { encSolver = solver
    , encAddPBAtLeast = Nothing
    , encUsePB  = usePBRef
    , encConjTable = table
    , encITETable = table2
    }

-- | Create a @Encoder@ instance.
-- If the encoder is built using this function, 'setUsePB' has an effect.
newEncoderWithPBLin :: PrimMonad m => SAT.AddPBLin m a => a -> m (Encoder m)
newEncoderWithPBLin solver = do
  usePBRef <- newMutVar False
  table <- newMutVar Map.empty
  table2 <- newMutVar Map.empty
  return $
    Encoder
    { encSolver = solver
    , encAddPBAtLeast = Just (SAT.addPBAtLeast solver)
    , encUsePB  = usePBRef
    , encConjTable = table
    , encITETable = table2
    }

-- | Use /pseudo boolean constraints/ or use only /clauses/.
-- This option has an effect only when the encoder is built using 'newEncoderWithPBLin'.
setUsePB :: PrimMonad m => Encoder m -> Bool -> m ()
setUsePB encoder usePB = writeMutVar (encUsePB encoder) usePB

-- | Assert a given formula to underlying SAT solver by using
-- Tseitin encoding.
addFormula :: PrimMonad m => Encoder m -> Formula -> m ()
addFormula encoder formula = do
  case formula of
    And xs -> mapM_ (addFormula encoder) xs
    Equiv a b -> do
      lit1 <- encodeFormula encoder a
      lit2 <- encodeFormula encoder b
      SAT.addClause encoder [SAT.litNot lit1, lit2] -- a→b
      SAT.addClause encoder [SAT.litNot lit2, lit1] -- b→a
    Not (Not a)     -> addFormula encoder a
    Not (Or xs)     -> addFormula encoder (andB (map notB xs))
    Not (Imply a b) -> addFormula encoder (a .&&. notB b)
    Not (Equiv a b) -> do
      lit1 <- encodeFormula encoder a
      lit2 <- encodeFormula encoder b
      SAT.addClause encoder [lit1, lit2] -- a ∨ b
      SAT.addClause encoder [SAT.litNot lit1, SAT.litNot lit2] -- ¬a ∨ ¬b
    _ -> do
      c <- encodeToClause encoder formula
      SAT.addClause encoder c

encodeToClause :: PrimMonad m => Encoder m -> Formula -> m SAT.Clause
encodeToClause encoder formula =
  case formula of
    And [x] -> encodeToClause encoder x
    Or xs -> do
      cs <- mapM (encodeToClause encoder) xs
      return $ concat cs
    Not (Not x)  -> encodeToClause encoder x
    Not (And xs) -> do
      encodeToClause encoder (orB (map notB xs))
    Imply a b -> do
      encodeToClause encoder (notB a .||. b)
    _ -> do
      l <- encodeFormulaWithPolarity encoder polarityPos formula
      return [l]

encodeFormula :: PrimMonad m => Encoder m -> Formula -> m SAT.Lit
encodeFormula encoder = encodeFormulaWithPolarity encoder polarityBoth

encodeFormulaWithPolarity :: PrimMonad m => Encoder m -> Polarity -> Formula -> m SAT.Lit
encodeFormulaWithPolarity encoder p formula = do
  case formula of
    Atom l -> return l
    And xs -> encodeConjWithPolarity encoder p =<< mapM (encodeFormulaWithPolarity encoder p) xs
    Or xs  -> encodeDisjWithPolarity encoder p =<< mapM (encodeFormulaWithPolarity encoder p) xs
    Not x -> liftM SAT.litNot $ encodeFormulaWithPolarity encoder (negatePolarity p) x
    Imply x y -> do
      encodeFormulaWithPolarity encoder p (notB x .||. y)
    Equiv x y -> do
      lit1 <- encodeFormulaWithPolarity encoder polarityBoth x
      lit2 <- encodeFormulaWithPolarity encoder polarityBoth y
      encodeFormulaWithPolarity encoder p $
        (Atom lit1 .=>. Atom lit2) .&&. (Atom lit2 .=>. Atom lit1)
    ITE c t e -> do
      c' <- encodeFormulaWithPolarity encoder polarityBoth c
      t' <- encodeFormulaWithPolarity encoder p t
      e' <- encodeFormulaWithPolarity encoder p e
      encodeITEWithPolarity encoder p c' t' e'

-- | Return an literal which is equivalent to a given conjunction.
--
-- @
--   encodeConj encoder = 'encodeConjWithPolarity' encoder 'polarityBoth'
-- @
encodeConj :: PrimMonad m => Encoder m -> [SAT.Lit] -> m SAT.Lit
encodeConj encoder = encodeConjWithPolarity encoder polarityBoth

-- | Return an literal which is equivalent to a given conjunction which occurs only in specified polarity.
encodeConjWithPolarity :: forall m. PrimMonad m => Encoder m -> Polarity -> [SAT.Lit] -> m SAT.Lit
encodeConjWithPolarity _ _ [l] =  return l
encodeConjWithPolarity encoder (Polarity pos neg) ls = do
  let ls2 = IntSet.fromList ls
  usePB <- readMutVar (encUsePB encoder)
  table <- readMutVar (encConjTable encoder)

  let -- If F is monotone, F(A ∧ B) ⇔ ∃x. F(x) ∧ (x → A∧B)
      definePos :: SAT.Lit -> m ()
      definePos l = do
        case encAddPBAtLeast encoder of
          Just addPBAtLeast | usePB -> do
            -- ∀i.(l → li) ⇔ Σli >= n*l ⇔ Σli - n*l >= 0
            let n = IntSet.size ls2
            addPBAtLeast ((- fromIntegral n, l) : [(1,li) | li <- IntSet.toList ls2]) 0
          _ -> do
            forM_ (IntSet.toList ls2) $ \li -> do
              -- (l → li)  ⇔  (¬l ∨ li)
              SAT.addClause encoder [SAT.litNot l, li]

      -- If F is anti-monotone, F(A ∧ B) ⇔ ∃x. F(x) ∧ (x ← A∧B) ⇔ ∃x. F(x) ∧ (x∨¬A∨¬B).
      defineNeg :: SAT.Lit -> m ()
      defineNeg l = do
        -- ((l1 ∧ l2 ∧ … ∧ ln) → l)  ⇔  (¬l1 ∨ ¬l2 ∨ … ∨ ¬ln ∨ l)
        SAT.addClause encoder (l : map SAT.litNot (IntSet.toList ls2))

  case Map.lookup ls2 table of
    Just (l, posDefined, negDefined) -> do
      when (pos && not posDefined) $ definePos l
      when (neg && not negDefined) $ defineNeg l
      when (posDefined < pos || negDefined < neg) $
        modifyMutVar (encConjTable encoder) (Map.insert ls2 (l, (max posDefined pos), (max negDefined neg)))
      return l
    Nothing -> do
      l <- SAT.newVar encoder
      when pos $ definePos l
      when neg $ defineNeg l
      modifyMutVar (encConjTable encoder) (Map.insert ls2 (l, pos, neg))
      return l

-- | Return an literal which is equivalent to a given disjunction.
--
-- @
--   encodeDisj encoder = 'encodeDisjWithPolarity' encoder 'polarityBoth'
-- @
encodeDisj :: PrimMonad m => Encoder m -> [SAT.Lit] -> m SAT.Lit
encodeDisj encoder = encodeDisjWithPolarity encoder polarityBoth

-- | Return an literal which is equivalent to a given disjunction which occurs only in specified polarity.
encodeDisjWithPolarity :: PrimMonad m => Encoder m -> Polarity -> [SAT.Lit] -> m SAT.Lit
encodeDisjWithPolarity _ _ [l] =  return l
encodeDisjWithPolarity encoder p ls = do
  -- ¬l ⇔ ¬(¬l1 ∧ … ∧ ¬ln) ⇔ (l1 ∨ … ∨ ln)
  l <- encodeConjWithPolarity encoder (negatePolarity p) [SAT.litNot li | li <- ls]
  return $ SAT.litNot l

-- | Return an literal which is equivalent to a given if-then-else.
--
-- @
--   encodeITE encoder = 'encodeITEWithPolarity' encoder 'polarityBoth'
-- @
encodeITE :: PrimMonad m => Encoder m -> SAT.Lit -> SAT.Lit -> SAT.Lit -> m SAT.Lit
encodeITE encoder = encodeITEWithPolarity encoder polarityBoth

-- | Return an literal which is equivalent to a given if-then-else which occurs only in specified polarity.
encodeITEWithPolarity :: forall m. PrimMonad m => Encoder m -> Polarity -> SAT.Lit -> SAT.Lit -> SAT.Lit -> m SAT.Lit
encodeITEWithPolarity encoder p c t e | c < 0 =
  encodeITEWithPolarity encoder p (- c) e t
encodeITEWithPolarity encoder (Polarity pos neg) c t e = do
  table <- readMutVar (encITETable encoder)

  let definePos :: SAT.Lit -> m ()
      definePos x = do
        -- x → ite(c,t,e)
        -- ⇔ x → (c∧t ∨ ¬c∧e)
        -- ⇔ (x∧c → t) ∧ (x∧¬c → e)
        -- ⇔ (¬x∨¬c∨t) ∧ (¬x∨c∨e)
        SAT.addClause encoder [-x, -c, t]
        SAT.addClause encoder [-x, c, e]
        SAT.addClause encoder [t, e, -x] -- redundant, but will increase the strength of unit propagation.
  
      defineNeg :: SAT.Lit -> m ()
      defineNeg x = do
        -- ite(c,t,e) → x
        -- ⇔ (c∧t ∨ ¬c∧e) → x
        -- ⇔ (c∧t → x) ∨ (¬c∧e →x)
        -- ⇔ (¬c∨¬t∨x) ∨ (c∧¬e∨x)
        SAT.addClause encoder [-c, -t, x]
        SAT.addClause encoder [c, -e, x]
        SAT.addClause encoder [-t, -e, x] -- redundant, but will increase the strength of unit propagation.

  case Map.lookup (c,t,e) table of
    Just (l, posDefined, negDefined) -> do
      when (pos && not posDefined) $ definePos l
      when (neg && not negDefined) $ defineNeg l
      when (posDefined < pos || negDefined < neg) $
        modifyMutVar (encITETable encoder) (Map.insert (c,t,e) (l, (max posDefined pos), (max negDefined neg)))
      return l
    Nothing -> do
      l <- SAT.newVar encoder
      when pos $ definePos l
      when neg $ defineNeg l
      modifyMutVar (encITETable encoder) (Map.insert (c,t,e) (l, pos, neg))
      return l


getDefinitions :: PrimMonad m => Encoder m -> m [(SAT.Lit, Formula)]
getDefinitions encoder = do
  t <- readMutVar (encConjTable encoder)
  return $ [(l, andB [Atom l1 | l1 <- IntSet.toList ls]) | (ls, (l, _, _)) <- Map.toList t]


data Polarity
  = Polarity
  { polarityPosOccurs :: Bool
  , polarityNegOccurs :: Bool
  }
  deriving (Eq, Show)

negatePolarity :: Polarity -> Polarity
negatePolarity (Polarity pos neg) = (Polarity neg pos)

polarityPos :: Polarity
polarityPos = Polarity True False

polarityNeg :: Polarity
polarityNeg = Polarity False True

polarityBoth :: Polarity
polarityBoth = Polarity True True

polarityNone :: Polarity
polarityNone = Polarity False False

