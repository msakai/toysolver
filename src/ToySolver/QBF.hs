{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE BangPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.QBF
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (BangPatterns)
--
-- Reference:
--
-- * Mikoláš Janota, William Klieber, Joao Marques-Silva, Edmund Clarke.
--   Solving QBF with Counterexample Guided Refinement.
--   In Theory and Applications of Satisfiability Testing (SAT 2012), pp. 114-128.
--   <http://dx.doi.org/10.1007/978-3-642-31612-8_10>
--   <https://www.cs.cmu.edu/~wklieber/papers/qbf-cegar-sat-2012.pdf>
--
-----------------------------------------------------------------------------
module ToySolver.QBF
  ( Quantifier (..)
  , Prefix
  , normalizePrefix
  , quantifyFreeVariables 
  , Matrix
  , solve
  , solveNaive
  , solveCEGAR
  , solveCEGARIncremental
  , solveQE
  , solveQE_CNF
  , solveDDR
  ) where

import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Trans.Except
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Function (on)
import Data.List (groupBy, foldl')
import Data.Maybe

import ToySolver.Data.Boolean
import ToySolver.Data.BoolExpr (BoolExpr)
import qualified ToySolver.Data.BoolExpr as BoolExpr
import qualified ToySolver.SAT as SAT
import ToySolver.SAT.Types (LitSet, VarSet, VarMap)
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import ToySolver.SAT.Store.CNF

import qualified ToySolver.SAT.ExistentialQuantification as QE
import ToySolver.Text.CNF (Quantifier (..))
import qualified ToySolver.Text.CNF as CNF

-- ----------------------------------------------------------------------------

type Prefix = [(Quantifier, VarSet)]

normalizePrefix :: Prefix -> Prefix
normalizePrefix = groupQuantifiers . removeEmptyQuantifiers

removeEmptyQuantifiers :: Prefix -> Prefix
removeEmptyQuantifiers = filter (\(_,xs) -> not (IntSet.null xs))

groupQuantifiers :: Prefix -> Prefix
groupQuantifiers = map f . groupBy ((==) `on` fst)
  where
    f qs = (fst (head qs), IntSet.unions [xs | (_,xs) <- qs])

quantifyFreeVariables :: Int -> Prefix -> Prefix
quantifyFreeVariables nv prefix
  | IntSet.null rest = prefix
  | otherwise = (E, rest) : prefix
  where
    rest = IntSet.fromList [1..nv] `IntSet.difference` IntSet.unions [vs | (_q, vs) <- prefix]

prefixStartWithA :: Prefix -> Bool
prefixStartWithA ((A,_) : _) = True
prefixStartWithA _ = False

prefixStartWithE :: Prefix -> Bool
prefixStartWithE ((E,_) : _) = True
prefixStartWithE _ = False

-- ----------------------------------------------------------------------------

type Matrix = BoolExpr SAT.Lit

reduct :: Matrix -> LitSet -> Matrix
reduct m ls = BoolExpr.simplify $ m >>= s
  where
    s l
      |   l  `IntSet.member` ls = true
      | (-l) `IntSet.member` ls = false
      | otherwise = BoolExpr.Atom l

substVarMap :: Matrix -> VarMap Matrix -> Matrix
substVarMap m s = BoolExpr.simplify $ m >>= \l -> do
  let v = abs l
  (if l > 0 then id else notB) $ IntMap.findWithDefault (BoolExpr.Atom v) v s

-- XXX
prenexAnd :: (Int, Prefix, Matrix) -> (Int, Prefix, Matrix) -> (Int, Prefix, Matrix)
prenexAnd (nv1, prefix1, matrix1) (nv2, prefix2, matrix2) =
  evalState (f [] IntSet.empty IntMap.empty IntMap.empty prefix1 prefix2) (nv1 `max` nv2)
  where
    f :: Prefix -> VarSet
      -> VarMap (BoolExpr SAT.Lit) -> VarMap (BoolExpr SAT.Lit)
      -> Prefix -> Prefix
      -> State Int (Int, Prefix, Matrix)
    f prefix _bvs subst1 subst2 [] [] = do
      nv <- get
      return (nv, prefix, BoolExpr.simplify (substVarMap matrix1 subst1 .&&. substVarMap matrix2 subst2))
    f prefix bvs subst1 subst2 ((A,xs1) : prefix1') ((A,xs2) : prefix2') = do
      let xs = IntSet.union xs1 xs2
          ys = IntSet.intersection bvs xs
      nv <- get
      put (nv + IntSet.size ys)
      let s  = IntMap.fromList $ zip (IntSet.toList ys) [(nv+1) ..]
          xs' = (xs `IntSet.difference` bvs) `IntSet.union` IntSet.fromList (IntMap.elems s)
          subst1' = fmap BoolExpr.Atom (IntMap.filterWithKey (\x _ -> x `IntSet.member` xs1) s) `IntMap.union` subst1
          subst2' = fmap BoolExpr.Atom (IntMap.filterWithKey (\x _ -> x `IntSet.member` xs2) s) `IntMap.union` subst2
      f (prefix ++ [(A, xs')]) (bvs `IntSet.union` xs') subst1' subst2' prefix1' prefix2'
    f prefix bvs subst1 subst2 ((q,xs) : prefix1') prefix2 | q==E || not (prefixStartWithE prefix2) = do
      let ys = IntSet.intersection bvs xs
      nv <- get
      put (nv + IntSet.size ys)
      let s  = IntMap.fromList $ zip (IntSet.toList ys) [(nv+1) ..]
          xs' = (xs `IntSet.difference` bvs) `IntSet.union` IntSet.fromList (IntMap.elems s)
          subst1' = fmap BoolExpr.Atom s `IntMap.union` subst1
      f (prefix ++ [(q, xs')]) (bvs `IntSet.union` xs') subst1' subst2 prefix1' prefix2
    f prefix bvs subst1 subst2 prefix1 ((q,xs) : prefix2')  = do
      let ys = IntSet.intersection bvs xs
      nv <- get
      put (nv + IntSet.size ys)
      let s  = IntMap.fromList $ zip (IntSet.toList ys) [(nv+1) ..]
          xs' = (xs `IntSet.difference` bvs) `IntSet.union` IntSet.fromList (IntMap.elems s)
          subst2' = fmap BoolExpr.Atom s `IntMap.union` subst2
      f (prefix ++ [(q, xs')]) (bvs `IntSet.union` xs') subst1 subst2' prefix1 prefix2'

-- XXX     
prenexOr :: (Int, Prefix, Matrix) -> (Int, Prefix, Matrix) -> (Int, Prefix, Matrix)
prenexOr (nv1, prefix1, matrix1) (nv2, prefix2, matrix2) =
  evalState (f [] IntSet.empty IntMap.empty IntMap.empty prefix1 prefix2) (nv1 `max` nv2)
  where
    f :: Prefix -> VarSet
      -> VarMap (BoolExpr SAT.Lit) -> VarMap (BoolExpr SAT.Lit)
      -> Prefix -> Prefix
      -> State Int (Int, Prefix, Matrix)
    f prefix _bvs subst1 subst2 [] [] = do
      nv <- get
      return (nv, prefix, BoolExpr.simplify (substVarMap matrix1 subst1 .||. substVarMap matrix2 subst2))
    f prefix bvs subst1 subst2 ((E,xs1) : prefix1') ((E,xs2) : prefix2') = do
      let xs = IntSet.union xs1 xs2
          ys = IntSet.intersection bvs xs
      nv <- get
      put (nv + IntSet.size ys)
      let s  = IntMap.fromList $ zip (IntSet.toList ys) [(nv+1) ..]
          xs' = (xs `IntSet.difference` bvs) `IntSet.union` IntSet.fromList (IntMap.elems s)
          subst1' = fmap BoolExpr.Atom (IntMap.filterWithKey (\x _ -> x `IntSet.member` xs1) s) `IntMap.union` subst1
          subst2' = fmap BoolExpr.Atom (IntMap.filterWithKey (\x _ -> x `IntSet.member` xs2) s) `IntMap.union` subst2
      f (prefix ++ [(A, xs')]) (bvs `IntSet.union` xs') subst1' subst2' prefix1' prefix2'
    f prefix bvs subst1 subst2 ((q,xs) : prefix1') prefix2 | q==A || not (prefixStartWithA prefix2)= do
      let ys = IntSet.intersection bvs xs
      nv <- get
      put (nv + IntSet.size ys)
      let s  = IntMap.fromList $ zip (IntSet.toList ys) [(nv+1) ..]
          xs' = (xs `IntSet.difference` bvs) `IntSet.union` IntSet.fromList (IntMap.elems s)
          subst1' = fmap BoolExpr.Atom s `IntMap.union` subst1
      f (prefix ++ [(q, xs')]) (bvs `IntSet.union` xs') subst1' subst2 prefix1' prefix2
    f prefix bvs subst1 subst2 prefix1 ((q,xs) : prefix2')  = do
      let ys = IntSet.intersection bvs xs
      nv <- get
      put (nv + IntSet.size ys)
      let s  = IntMap.fromList $ zip (IntSet.toList ys) [(nv+1) ..]
          xs' = (xs `IntSet.difference` bvs) `IntSet.union` IntSet.fromList (IntMap.elems s)
          subst2' = fmap BoolExpr.Atom s `IntMap.union` subst2
      f (prefix ++ [(q, xs')]) (bvs `IntSet.union` xs') subst1 subst2' prefix1 prefix2'

-- ----------------------------------------------------------------------------

solve :: Int -> Prefix -> Matrix -> IO (Bool, Maybe LitSet)
solve = solveCEGARIncremental

-- ----------------------------------------------------------------------------

-- | Naive Algorithm for a Winning Move
solveNaive :: Int -> Prefix -> Matrix -> IO (Bool, Maybe LitSet)
solveNaive nv prefix matrix =
  case prefix' of
    [] -> if BoolExpr.fold undefined matrix
          then return (True, Just IntSet.empty)
          else return (False, Nothing)
    (E,_) : _ -> do
      m <- f prefix' matrix
      return (isJust m, m)
    (A,_) : _ -> do
      m <- f prefix' matrix
      return (isNothing m, m)
  where
    prefix' = normalizePrefix prefix

    {- Naive Algorithm for a Winning Move
    Function Solve (QX. Φ)
    begin
      if Φ has no quant then
        return (Q = ∃) ? SAT(φ) : SAT(¬φ)
      Λ ← {true, false}^X  // consider all assignments
      while true do
        if Λ = ∅ then      // all assignments used up
          return NULL
        τ ← pick(Λ)        // pick a candidate solution
        μ ← Solve(Φ[τ])    // find a countermove
        if μ = NULL then   // winning move
          return τ
        Λ ← Λ \ {τ}        // remove bad candidate
      end
    end
    -}
    f :: Prefix -> Matrix -> IO (Maybe LitSet)
    f [] _matrix = error "should not happen"
    f [(q,xs)] matrix = do
      solver <- SAT.newSolver
      SAT.newVars_ solver nv
      enc <- Tseitin.newEncoder solver
      case q of
        E -> Tseitin.addFormula enc matrix
        A -> Tseitin.addFormula enc (notB matrix)
      ret <- SAT.solve solver
      if ret then do
        m <- SAT.getModel solver
        return $ Just $ IntSet.fromList [if SAT.evalLit m x then x else -x | x <- IntSet.toList xs]
      else
        return Nothing
    f ((_q,xs) : prefix') matrix = do
      ret <- runExceptT $ do
        let moves :: [LitSet]
            moves = map IntSet.fromList $ sequence [[x, -x] | x <- IntSet.toList xs]
        forM_ moves $ \tau -> do
          ret <- lift $ f prefix' (reduct matrix tau)
          case ret of
            Nothing  -> throwE tau
            Just _nu -> return ()
      case ret of
        Left tau -> return (Just tau)
        Right () -> return Nothing

-- ----------------------------------------------------------------------------

-- | Abstraction-Based Algorithm for a Winning Move                    
solveCEGAR :: Int -> Prefix -> Matrix -> IO (Bool, Maybe LitSet)
solveCEGAR nv prefix matrix =
  case prefix' of
    [] -> if BoolExpr.fold undefined matrix
          then return (True, Just IntSet.empty)
          else return (False, Nothing)
    (E,_) : _ -> do
      m <- f nv prefix' matrix
      return (isJust m, m)
    (A,_) : _ -> do
      m <- f nv prefix' matrix
      return (isNothing m, m)
  where
    prefix' = normalizePrefix prefix

    {-
    Function Solve (QX. Φ)
    begin
      if Φ has no quant then
        return (Q = ∃) ? SAT(φ) : SAT(¬φ)
      ω ← ∅
      while true do
        α ← (Q = ∃) ? ∧_{μ∈ω} Φ[μ] : ∨_{μ∈ω} Φ[μ] // abstraction
        τ' ← Solve(Prenex(QX.α)) // find a candidate
        if τ' = NULL then return NULL // no winning move
        τ ← {l | l ∈ τ′ ∧ var(l) ∈ X} // filter a move for X
        μ ← Solve(Φ[τ])
        if μ = NULL then return τ
        ω ← ω∪{μ}
      end
    end
    -}
    f :: Int -> Prefix -> Matrix -> IO (Maybe LitSet)
    f _nv [] _matrix = error "should not happen"
    f nv [(q,xs)] matrix = do
      solver <- SAT.newSolver
      SAT.newVars_ solver nv
      enc <- Tseitin.newEncoder solver
      case q of
        E -> Tseitin.addFormula enc matrix
        A -> Tseitin.addFormula enc (notB matrix)
      ret <- SAT.solve solver
      if ret then do
        m <- SAT.getModel solver
        return $ Just $ IntSet.fromList [if SAT.evalLit m x then x else -x | x <- IntSet.toList xs]
      else
        return Nothing
    f nv ((q,xs) : prefix'@((_q2,_) : prefix'')) matrix = do
      let loop counterMoves = do
            let ys = [(nv, prefix'', reduct matrix nu) | nu <- counterMoves]
                (nv2, prefix2, matrix2) =
                  if q==E
                  then foldl' prenexAnd (nv,[],true) ys
                  else foldl' prenexOr (nv,[],false) ys
            ret <- f nv2 (normalizePrefix ((q,xs) : prefix2)) matrix2
            case ret of
              Nothing -> return Nothing
              Just tau' -> do
                let tau = IntSet.filter (\l -> abs l `IntSet.member` xs) tau'
                ret2 <- f nv prefix' (reduct matrix tau)
                case ret2 of
                  Nothing -> return (Just tau)
                  Just nu -> loop (nu : counterMoves)
      loop []

-- ----------------------------------------------------------------------------

-- | Abstraction-Based Algorithm for a Winning Move
solveCEGARIncremental :: Int -> Prefix -> Matrix -> IO (Bool, Maybe LitSet)
solveCEGARIncremental nv prefix matrix =
  case prefix' of
    [] -> if BoolExpr.fold undefined matrix
          then return (True, Just IntSet.empty)
          else return (False, Nothing)
    (E,_) : _ -> do
      m <- f nv IntSet.empty prefix' matrix
      return (isJust m, m)
    (A,_) : _ -> do
      m <- f nv IntSet.empty prefix' matrix
      return (isNothing m, m)
  where
    prefix' = normalizePrefix prefix

    {-
    Function Solve (QX. Φ)
    begin
      if Φ has no quant then
        return (Q = ∃) ? SAT(φ) : SAT(¬φ)
      ω ← ∅
      while true do
        α ← (Q = ∃) ? ∧_{μ∈ω} Φ[μ] : ∨_{μ∈ω} Φ[μ] // abstraction
        τ' ← Solve(Prenex(QX.α)) // find a candidate
        if τ' = NULL then return NULL // no winning move
        τ ← {l | l ∈ τ′ ∧ var(l) ∈ X} // filter a move for X
        μ ← Solve(Φ[τ])
        if μ = NULL then return τ
        ω ← ω∪{μ}
      end
    end
    -}
    f :: Int -> LitSet -> Prefix -> Matrix -> IO (Maybe LitSet)
    f nv assumptions prefix matrix = do
      solver <- SAT.newSolver
      SAT.newVars_ solver nv
      enc <- Tseitin.newEncoder solver
      xs <-
        case last prefix of
          (E, xs) -> do
            Tseitin.addFormula enc matrix
            return xs
          (A, xs) -> do
            Tseitin.addFormula enc (notB matrix)
            return xs
      let g :: Int -> LitSet -> Prefix -> Matrix -> IO (Maybe LitSet)
          g _nv _assumptions [] _matrix = error "should not happen"
          g nv assumptions [(q,xs)] matrix = do
            ret <- SAT.solveWith solver (IntSet.toList assumptions)
            if ret then do
              m <- SAT.getModel solver
              return $ Just $ IntSet.fromList [if SAT.evalLit m x then x else -x | x <- IntSet.toList xs]
            else
              return Nothing            
          g nv assumptions prefix@((q,xs) : prefix'@((_q2,_) : prefix'')) matrix = do
            let loop counterMoves = do
                  let ys = [(nv, prefix'', reduct matrix nu) | nu <- counterMoves]
                      (nv2, prefix2, matrix2) =
                        if q==E
                        then foldl' prenexAnd (nv,[],true) ys
                        else foldl' prenexOr (nv,[],false) ys
                  ret <- f nv2 assumptions (normalizePrefix ((q,xs) : prefix2)) matrix2
                  case ret of
                    Nothing -> return Nothing
                    Just tau' -> do
                      let tau = IntSet.filter (\l -> abs l `IntSet.member` xs) tau'
                      ret2 <- g nv (assumptions `IntSet.union` tau) prefix' (reduct matrix tau)
                      case ret2 of
                        Nothing -> return (Just tau)
                        Just nu -> loop (nu : counterMoves)
            loop []
      g nv IntSet.empty prefix matrix

-- ----------------------------------------------------------------------------

data CNFOrDNF
  = CNF [LitSet]
  | DNF [LitSet]
  deriving (Show)

negateCNFOrDNF :: CNFOrDNF -> CNFOrDNF
negateCNFOrDNF (CNF xss) = DNF (map (IntSet.map negate) xss)
negateCNFOrDNF (DNF xss) = CNF (map (IntSet.map negate) xss)

toCNF :: Int -> CNFOrDNF -> CNF.CNF
toCNF nv (CNF clauses) = CNF.CNF nv (length clauses) (map (SAT.packClause . IntSet.toList) clauses)
toCNF nv (DNF [])    = CNF.CNF nv 1 [SAT.packClause []]
toCNF nv (DNF cubes) = CNF.CNF (nv + length cubes) (length cs) (map SAT.packClause cs)
  where
    zs = zip [nv+1..] cubes
    cs = map fst zs : [[-sel, lit] | (sel, cube) <- zs, lit <- IntSet.toList cube]

solveQE :: Int -> Prefix -> Matrix -> IO (Bool, Maybe LitSet)
solveQE nv prefix matrix = do
  store <- newCNFStore
  SAT.newVars_ store nv
  encoder <- Tseitin.newEncoder store
  Tseitin.addFormula encoder matrix
  cnf <- getCNFFormula store
  let prefix' =
        if CNF.cnfNumVars cnf > nv then
          prefix ++ [(E, IntSet.fromList [nv+1 .. CNF.cnfNumVars cnf])]
        else
          prefix
  (b, m) <- solveQE_CNF (CNF.cnfNumVars cnf) prefix' (map SAT.unpackClause (CNF.cnfClauses cnf))
  return (b, fmap (IntSet.filter (\lit -> abs lit <= nv)) m)

solveQE_CNF :: Int -> Prefix -> [SAT.Clause] -> IO (Bool, Maybe LitSet)
solveQE_CNF nv prefix matrix = g (normalizePrefix prefix) matrix
  where
    g :: Prefix -> [SAT.Clause] -> IO (Bool, Maybe LitSet)
    g ((E,xs) : prefix') matrix = do
      cnf <- liftM (toCNF nv) $ f prefix' matrix
      solver <- SAT.newSolver
      SAT.newVars_ solver (CNF.cnfNumVars cnf)
      forM_ (CNF.cnfClauses cnf) $ \clause -> do
        SAT.addClause solver (SAT.unpackClause clause)
      ret <- SAT.solve solver
      if ret then do
        m <- SAT.getModel solver
        return (True, Just $ IntSet.fromList [if SAT.evalLit m x then x else -x | x <- IntSet.toList xs])
      else do
        return (False, Nothing)
    g ((A,xs) : prefix') matrix = do
      cnf <- liftM (toCNF nv . negateCNFOrDNF) $ f prefix' matrix
      solver <- SAT.newSolver
      SAT.newVars_ solver (CNF.cnfNumVars cnf)
      forM_ (CNF.cnfClauses cnf) $ \clause -> do
        SAT.addClause solver (SAT.unpackClause clause)
      ret <- SAT.solve solver
      if ret then do
        m <- SAT.getModel solver
        return (False, Just $ IntSet.fromList [if SAT.evalLit m x then x else -x | x <- IntSet.toList xs])
      else do
        return (True, Nothing)
    g prefix matrix = do
      ret <- f prefix matrix
      case ret of
        CNF xs -> return (not (any IntSet.null xs), Nothing)
        DNF xs -> return (any IntSet.null xs, Nothing)

    f :: Prefix -> [SAT.Clause] -> IO CNFOrDNF
    f [] matrix = return $ CNF [IntSet.fromList clause | clause <- matrix]
    f ((E,xs) : prefix') matrix = do
      cnf <- liftM (toCNF nv) $ f prefix' matrix
      dnf <- QE.shortestImplicantsE (xs `IntSet.union` IntSet.fromList [nv+1 .. CNF.cnfNumVars cnf]) cnf
      return $ DNF dnf
    f ((A,xs) : prefix') matrix = do
      cnf <- liftM (toCNF nv . negateCNFOrDNF) $ f prefix' matrix
      dnf <- QE.shortestImplicantsE (xs `IntSet.union` IntSet.fromList [nv+1 .. CNF.cnfNumVars cnf]) cnf
      return $ negateCNFOrDNF $ DNF dnf

-- ----------------------------------------------------------------------------

solveDDR :: Int -> Prefix -> Matrix -> IO (Bool, Maybe LitSet)
solveDDR nv prefix matrix = do
  let prefix' = normalizePrefix prefix

      -- TODO: use Array
      binderIndexTable :: IntMap Int
      binderIndexTable = IntMap.fromList [(v,i) | (i,(_,vs)) <- zip [0..] prefix', v <- IntSet.toList vs]

      -- TODO: use Array
      binderIndexToVars :: IntMap (Quantifier, VarSet)
      binderIndexToVars = IntMap.fromList [(i,b) | (i,b) <- zip [0..] prefix']

  store <- newCNFStore
  SAT.newVars_ store (nv*2)
  encoder <- Tseitin.newEncoder store
  Tseitin.addFormula encoder matrix
  cnf1 <- getCNFFormula store

  print cnf1

  store <- newCNFStore
  SAT.newVars_ store (nv*2)
  encoder <- Tseitin.newEncoder store
  Tseitin.addFormula encoder (BoolExpr.Not matrix)
  cnf2 <- getCNFFormula store

  print cnf2

  solver1 <- SAT.newSolver
  -- dual rail encoding
  SAT.newVars_ solver1 (CNF.cnfNumVars cnf1)
  forM_ [1..nv] $ \i -> do
    SAT.addClause solver1 [- i, - (nv + i)]
  forM_ (CNF.cnfClauses cnf1) $ \clause -> do
    SAT.addClause solver1 $ [if abs l <= nv then (if l > 0 then l else nv - l) else l | l <- SAT.unpackClause clause]

  solver2 <- SAT.newSolver
  -- dual rail encoding
  SAT.newVars_ solver2 (CNF.cnfNumVars cnf2)
  forM_ [1..nv] $ \i -> do
    SAT.addClause solver2 [- i, - (nv + i)]
  forM_ (CNF.cnfClauses cnf2) $ \clause -> do
    SAT.addClause solver2 [if abs l <= nv then (if l > 0 then l else nv - l) else l | l <- SAT.unpackClause clause]

  let opponent :: Quantifier -> Quantifier
      opponent E = A
      opponent A = E

      loop :: Quantifier -> IO (Quantifier, Maybe LitSet)
      loop q = do
        let solver =
              case q of
                E -> solver1
                A -> solver2
        b <- SAT.solve solver 
        if not b then do
          -- 相手の選択によらず自分の負け
          return (opponent q, Nothing)
        else do
          m <- SAT.getModel solver
          let -- TODO: minimize implicant
              implicant :: [SAT.Lit]
              implicant = concat
                          [ if SAT.evalLit m i then [i]
                            else if SAT.evalLit m (nv+i) then [-i]
                            else []
                          | i <- [1..nv]
                          ]
              binderIndexes = IntSet.fromList [binderIndexTable IntMap.! abs l | l <- implicant]
              binderIndexesOpponent = IntSet.filter (\i -> fst (binderIndexToVars IntMap.! i) == opponent q) binderIndexes
          if IntSet.null binderIndexesOpponent then do
            -- 相手の選択に無関係に充足可能なため
            return (q, Nothing)
          else do
            let j = IntSet.findMax binderIndexesOpponent
                solverO = case q of
                            E -> solver2
                            A -> solver1
                -- 相手方の最後の選択までの部分集合
                ls = [l | l <- implicant, binderIndexTable IntMap.! (abs l) <= j]
            print (opponent q, [if l > 0 then l else nv - l | l <- ls])
            SAT.addClause solverO [if l > 0 then l else nv - l | l <- ls]
            loop (opponent q)

  (q,witness) <- loop E
  return (q==E, witness)

-- ----------------------------------------------------------------------------

-- ∀y ∃x. x ∧ (y ∨ ¬x)
test = solveNaive 2 [(A, IntSet.singleton 2), (E, IntSet.singleton 1)] (x .&&. (y .||. notB x))
  where
    x  = BoolExpr.Atom 1
    y  = BoolExpr.Atom 2

test' = solveCEGAR 2 [(A, IntSet.singleton 2), (E, IntSet.singleton 1)] (x .&&. (y .||. notB x))
  where
    x  = BoolExpr.Atom 1
    y  = BoolExpr.Atom 2

test1 = prenexAnd (1, [(A, IntSet.singleton 1)], BoolExpr.Atom 1) (1, [(A, IntSet.singleton 1)], notB (BoolExpr.Atom 1))

test2 = prenexOr (1, [(A, IntSet.singleton 1)], BoolExpr.Atom 1) (1, [(A, IntSet.singleton 1)], BoolExpr.Atom 1)
