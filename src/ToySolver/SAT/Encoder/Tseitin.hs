{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Encoder.Tseitin
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
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
-- * [ES06] N. Eén and N. Sörensson. Translating Pseudo-Boolean
--   Constraints into SAT. JSAT 2:1–26, 2006.
--
-----------------------------------------------------------------------------
module ToySolver.SAT.Encoder.Tseitin
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
  , encodeXOR
  , encodeXORWithPolarity
  , encodeFASum
  , encodeFASumWithPolarity
  , encodeFACarry
  , encodeFACarryWithPolarity

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
  { encBase :: a
  , encAddPBAtLeast :: Maybe (SAT.PBLinSum -> Integer -> m ())
  , encUsePB     :: !(MutVar (PrimState m) Bool)
  , encConjTable :: !(MutVar (PrimState m) (Map SAT.LitSet (SAT.Var, Bool, Bool)))
  , encITETable  :: !(MutVar (PrimState m) (Map (SAT.Lit, SAT.Lit, SAT.Lit) (SAT.Var, Bool, Bool)))
  , encXORTable  :: !(MutVar (PrimState m) (Map (SAT.Lit, SAT.Lit) (SAT.Var, Bool, Bool)))
  , encFASumTable   :: !(MutVar (PrimState m) (Map (SAT.Lit, SAT.Lit, SAT.Lit) (SAT.Var, Bool, Bool)))
  , encFACarryTable :: !(MutVar (PrimState m) (Map (SAT.Lit, SAT.Lit, SAT.Lit) (SAT.Var, Bool, Bool)))
  }

instance Monad m => SAT.NewVar m (Encoder m) where
  newVar   Encoder{ encBase = a } = SAT.newVar a
  newVars  Encoder{ encBase = a } = SAT.newVars a
  newVars_ Encoder{ encBase = a } = SAT.newVars_ a

instance Monad m => SAT.AddClause m (Encoder m) where
  addClause Encoder{ encBase = a } = SAT.addClause a

-- | Create a @Encoder@ instance.
-- If the encoder is built using this function, 'setUsePB' has no effect.
newEncoder :: PrimMonad m => SAT.AddClause m a => a -> m (Encoder m)
newEncoder solver = do
  usePBRef <- newMutVar False
  tableConj <- newMutVar Map.empty
  tableITE <- newMutVar Map.empty
  tableXOR <- newMutVar Map.empty
  tableFASum <- newMutVar Map.empty
  tableFACarry <- newMutVar Map.empty
  return $
    Encoder
    { encBase = solver
    , encAddPBAtLeast = Nothing
    , encUsePB  = usePBRef
    , encConjTable = tableConj
    , encITETable = tableITE
    , encXORTable = tableXOR
    , encFASumTable = tableFASum
    , encFACarryTable = tableFACarry
    }

-- | Create a @Encoder@ instance.
-- If the encoder is built using this function, 'setUsePB' has an effect.
newEncoderWithPBLin :: PrimMonad m => SAT.AddPBLin m a => a -> m (Encoder m)
newEncoderWithPBLin solver = do
  usePBRef <- newMutVar False
  tableConj <- newMutVar Map.empty
  tableITE <- newMutVar Map.empty
  tableXOR <- newMutVar Map.empty
  tableFASum <- newMutVar Map.empty
  tableFACarry <- newMutVar Map.empty
  return $
    Encoder
    { encBase = solver
    , encAddPBAtLeast = Just (SAT.addPBAtLeast solver)
    , encUsePB  = usePBRef
    , encConjTable = tableConj
    , encITETable = tableITE
    , encXORTable = tableXOR
    , encFASumTable = tableFASum
    , encFACarryTable = tableFACarry
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
    ITE c t e -> do
      c' <- encodeFormula encoder c
      t' <- encodeFormulaWithPolarity encoder polarityPos t
      e' <- encodeFormulaWithPolarity encoder polarityPos e
      SAT.addClause encoder [-c', t'] --  c' → t'
      SAT.addClause encoder [ c', e'] -- ¬c' → e'
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

encodeWithPolarityHelper
  :: (PrimMonad m, Ord k)
  => Encoder m
  -> MutVar (PrimState m) (Map k (SAT.Var, Bool, Bool))
  -> (SAT.Lit -> m ()) -> (SAT.Lit -> m ())
  -> Polarity
  -> k
  -> m SAT.Var
encodeWithPolarityHelper encoder tableRef definePos defineNeg (Polarity pos neg) k = do
  table <- readMutVar tableRef
  case Map.lookup k table of
    Just (v, posDefined, negDefined) -> do
      when (pos && not posDefined) $ definePos v
      when (neg && not negDefined) $ defineNeg v
      when (posDefined < pos || negDefined < neg) $
        modifyMutVar' tableRef (Map.insert k (v, (max posDefined pos), (max negDefined neg)))
      return v
    Nothing -> do
      v <- SAT.newVar encoder
      when pos $ definePos v
      when neg $ defineNeg v
      modifyMutVar' tableRef (Map.insert k (v, pos, neg))
      return v


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
encodeConjWithPolarity encoder polarity ls = do
  usePB <- readMutVar (encUsePB encoder)
  table <- readMutVar (encConjTable encoder)
  let ls3 = IntSet.fromList ls
      ls2 = case Map.lookup IntSet.empty table of
              Nothing -> ls3
              Just (litTrue, _, _)
                | litFalse `IntSet.member` ls3 -> IntSet.singleton litFalse
                | otherwise -> IntSet.delete litTrue ls3
                where litFalse = SAT.litNot litTrue

  if IntSet.size ls2 == 1 then do
    return $ head $ IntSet.toList ls2
  else do
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
    encodeWithPolarityHelper encoder (encConjTable encoder) definePos defineNeg polarity ls2

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
encodeITEWithPolarity encoder polarity c t e = do
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

  encodeWithPolarityHelper encoder (encITETable encoder) definePos defineNeg polarity (c,t,e)

-- | Return an literal which is equivalent to an XOR of given two literals.
--
-- @
--   encodeXOR encoder = 'encodeXORWithPolarity' encoder 'polarityBoth'
-- @
encodeXOR :: PrimMonad m => Encoder m -> SAT.Lit -> SAT.Lit -> m SAT.Lit
encodeXOR encoder = encodeXORWithPolarity encoder polarityBoth

-- | Return an literal which is equivalent to an XOR of given two literals which occurs only in specified polarity.
encodeXORWithPolarity :: forall m. PrimMonad m => Encoder m -> Polarity -> SAT.Lit -> SAT.Lit -> m SAT.Lit
encodeXORWithPolarity encoder polarity a b = do
  let defineNeg x = do
        -- (a ⊕ b) → x
        SAT.addClause encoder [a, -b, x]   -- ¬a ∧  b → x
        SAT.addClause encoder [-a, b, x]   --  a ∧ ¬b → x
      definePos x = do
        -- x → (a ⊕ b)
        SAT.addClause encoder [a, b, -x]   -- ¬a ∧ ¬b → ¬x
        SAT.addClause encoder [-a, -b, -x] --  a ∧  b → ¬x
  encodeWithPolarityHelper encoder (encXORTable encoder) definePos defineNeg polarity (a,b)

-- | Return an "sum"-pin of a full-adder.
--
-- @
--   encodeFASum encoder = 'encodeFASumWithPolarity' encoder 'polarityBoth'
-- @
encodeFASum :: forall m. PrimMonad m => Encoder m -> SAT.Lit -> SAT.Lit -> SAT.Lit -> m SAT.Lit
encodeFASum encoder = encodeFASumWithPolarity encoder polarityBoth

-- | Return an "sum"-pin of a full-adder which occurs only in specified polarity.
encodeFASumWithPolarity :: forall m. PrimMonad m => Encoder m -> Polarity -> SAT.Lit -> SAT.Lit -> SAT.Lit -> m SAT.Lit
encodeFASumWithPolarity encoder polarity a b c = do
  let defineNeg x = do
        -- FASum(a,b,c) → x
        SAT.addClause encoder [-a,-b,-c,x] --  a ∧  b ∧  c → x
        SAT.addClause encoder [-a,b,c,x]   --  a ∧ ¬b ∧ ¬c → x
        SAT.addClause encoder [a,-b,c,x]   -- ¬a ∧  b ∧ ¬c → x
        SAT.addClause encoder [a,b,-c,x]   -- ¬a ∧ ¬b ∧  c → x
      definePos x = do
        -- x → FASum(a,b,c)
        -- ⇔ ¬FASum(a,b,c) → ¬x
        SAT.addClause encoder [a,b,c,-x]   -- ¬a ∧ ¬b ∧ ¬c → ¬x
        SAT.addClause encoder [a,-b,-c,-x] -- ¬a ∧  b ∧  c → ¬x
        SAT.addClause encoder [-a,b,-c,-x] --  a ∧ ¬b ∧  c → ¬x
        SAT.addClause encoder [-a,-b,c,-x] --  a ∧  b ∧ ¬c → ¬x
  encodeWithPolarityHelper encoder (encFASumTable encoder) definePos defineNeg polarity (a,b,c)

-- | Return an "carry"-pin of a full-adder.
--
-- @
--   encodeFACarry encoder = 'encodeFACarryWithPolarity' encoder 'polarityBoth'
-- @
encodeFACarry :: forall m. PrimMonad m => Encoder m -> SAT.Lit -> SAT.Lit -> SAT.Lit -> m SAT.Lit
encodeFACarry encoder = encodeFACarryWithPolarity encoder polarityBoth

-- | Return an "carry"-pin of a full-adder which occurs only in specified polarity.
encodeFACarryWithPolarity :: forall m. PrimMonad m => Encoder m -> Polarity -> SAT.Lit -> SAT.Lit -> SAT.Lit -> m SAT.Lit
encodeFACarryWithPolarity encoder polarity a b c = do
  let defineNeg x = do
        -- FACarry(a,b,c) → x
        SAT.addClause encoder [-a,-b,x] -- a ∧ b → x
        SAT.addClause encoder [-a,-c,x] -- a ∧ c → x
        SAT.addClause encoder [-b,-c,x] -- b ∧ c → x
      definePos x = do
        -- x → FACarry(a,b,c)
        -- ⇔ ¬FACarry(a,b,c) → ¬x
        SAT.addClause encoder [a,b,-x]  --  ¬a ∧ ¬b → ¬x
        SAT.addClause encoder [a,c,-x]  --  ¬a ∧ ¬c → ¬x
        SAT.addClause encoder [b,c,-x]  --  ¬b ∧ ¬c → ¬x
  encodeWithPolarityHelper encoder (encFACarryTable encoder) definePos defineNeg polarity (a,b,c)


getDefinitions :: PrimMonad m => Encoder m -> m [(SAT.Var, Formula)]
getDefinitions encoder = do
  tableConj <- readMutVar (encConjTable encoder)
  tableITE <- readMutVar (encITETable encoder)
  tableXOR <- readMutVar (encXORTable encoder)
  tableFASum <- readMutVar (encFASumTable encoder)
  tableFACarry <- readMutVar (encFACarryTable encoder)
  let m1 = [(v, andB [Atom l1 | l1 <- IntSet.toList ls]) | (ls, (v, _, _)) <- Map.toList tableConj]
      m2 = [(v, ite (Atom c) (Atom t) (Atom e)) | ((c,t,e), (v, _, _)) <- Map.toList tableITE]
      m3 = [(v, (Atom a .||. Atom b) .&&. (Atom (-a) .||. Atom (-b))) | ((a,b), (v, _, _)) <- Map.toList tableXOR]
      m4 = [(v, orB [andB [Atom l | l <- ls] | ls <- [[a,b,c],[a,-b,-c],[-a,b,-c],[-a,-b,c]]])
             | ((a,b,c), (v, _, _)) <- Map.toList tableFASum]
      m5 = [(v, orB [andB [Atom l | l <- ls] | ls <- [[a,b],[a,c],[b,c]]])
             | ((a,b,c), (v, _, _)) <- Map.toList tableFACarry]
  return $ concat [m1, m2, m3, m4, m5]


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

