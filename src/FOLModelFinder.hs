{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  FOLModelFinder
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (TypeSynonymInstances, FlexibleInstances)
--
-- A simple model finder.
--
-- References:
--
-- * Koen Claessen and Niklas Sörensson.
--   New Techniques that Improve MACE-style Finite Model Finding.
--   CADE-19. 2003.
--   <http://www.cs.miami.edu/~geoff/Conferences/CADE/Archive/CADE-19/WS4/04.pdf>
--
-----------------------------------------------------------------------------
module FOLModelFinder
  (
  -- * Formula types
    Var
  , FSym
  , PSym
  , GenLit (..)
  , Term (..)
  , Lit
  , Clause

  -- * Model types
  , Model (..)
  , Entity
  , showModel
  , showEntity

  -- * Main function
  , findModel
  ) where

import Control.Monad
import Control.Monad.State
import Data.Array.IArray
import Data.IORef
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Text.Printf

import qualified SAT

-- ---------------------------------------------------------------------------

-- | Variable
type Var = String

-- | Function Symbol
type FSym = String

-- | Predicate Symbol
type PSym = String

class Vars a where
  vars :: a -> Set.Set Var

instance Vars a => Vars [a] where
  vars = Set.unions . map vars

data GenLit a
  = Pos a
  | Neg a
  deriving (Show, Eq, Ord)

instance Vars a => Vars (GenLit a) where
  vars (Pos a) = vars a
  vars (Neg a) = vars a

-- ---------------------------------------------------------------------------

-- | Term
data Term
  = TmApp FSym [Term]
  | TmVar Var
  deriving (Show, Eq, Ord)

data Atom = PApp PSym [Term]
  deriving (Show, Eq, Ord)

type Lit = GenLit Atom
type Clause = [Lit]

instance Vars Term where
  vars (TmVar v)    = Set.singleton v
  vars (TmApp _ ts) = vars ts

instance Vars Atom where
  vars (PApp _ ts) = vars ts

-- ---------------------------------------------------------------------------

-- | Shallow term
data SGenTerm v
  = STmApp FSym [v]
  | STmVar v
  deriving (Show, Eq, Ord)

-- | Shallow atom
data SGenAtom v
  = SPApp PSym [v]
  | SEq (SGenTerm v) v
  deriving (Show, Eq, Ord)

type STerm   = SGenTerm Var
type SAtom   = SGenAtom Var
type SLit    = GenLit SAtom
type SClause = [SLit]

instance Vars STerm where
  vars (STmApp _ xs) = Set.fromList xs
  vars (STmVar v)    = Set.singleton v

instance Vars SAtom where
  vars (SPApp _ xs) = Set.fromList xs
  vars (SEq t v) = Set.insert v (vars t)

-- ---------------------------------------------------------------------------

type M = State (Set.Set Var, Int, [SLit])

flatten :: Clause -> SClause
flatten c =
  case runState (mapM flattenLit c) (vars c, 0, []) of
    (c, (_,_,ls)) -> removeNegEq $ ls ++ c
  where
    gensym :: M Var
    gensym = do
      (vs, n, ls) <- get
      let go m = do
            let v = "#" ++ show m
            if v `Set.member` vs
              then go (m+1)
              else do
                put (Set.insert v vs, m+1, ls)
                return v
      go n

    flattenLit :: Lit -> M SLit
    flattenLit (Pos a) = liftM Pos $ flattenAtom a
    flattenLit (Neg a) = liftM Neg $ flattenAtom a
    
    flattenAtom :: Atom -> M SAtom
    flattenAtom (PApp "=" [TmVar x, TmVar y])    = return $ SEq (STmVar x) y
    flattenAtom (PApp "=" [TmVar x, TmApp f ts]) = do
      xs <- mapM flattenTerm ts
      return $ SEq (STmApp f xs) x
    flattenAtom (PApp "=" [TmApp f ts, TmVar x]) = do
      xs <- mapM flattenTerm ts
      return $ SEq (STmApp f xs) x
    flattenAtom (PApp "=" [TmApp f ts, t2]) = do
      xs <- mapM flattenTerm ts
      x <- flattenTerm t2
      return $ SEq (STmApp f xs) x
    flattenAtom (PApp p ts) = do
      xs <- mapM flattenTerm ts
      return $ SPApp p xs
    
    flattenTerm :: Term -> M Var
    flattenTerm (TmVar x)    = return x
    flattenTerm (TmApp f ts) = do
      xs <- mapM flattenTerm ts
      x <- gensym
      (vs, n, ls) <- get
      put (vs, n, Neg (SEq (STmApp f xs) x) : ls)
      return x

    removeNegEq :: SClause -> SClause
    removeNegEq = go []
      where
        go r [] = r
        go r (Neg (SEq (STmVar x) y) : ls) = go (map (substLit x y) r) (map (substLit x y) ls)
        go r (l : ls) = go (l : r) ls

        substLit :: Var -> Var -> SLit -> SLit
        substLit x y (Pos a) = Pos $ substAtom x y a 
        substLit x y (Neg a) = Neg $ substAtom x y a

        substAtom :: Var -> Var -> SAtom -> SAtom
        substAtom x y (SPApp p xs) = SPApp p (map (substVar x y) xs)
        substAtom x y (SEq t v)    = SEq (substTerm x y t) (substVar x y v)

        substTerm :: Var -> Var -> STerm -> STerm
        substTerm x y (STmApp f xs) = STmApp f (map (substVar x y) xs)
        substTerm x y (STmVar v)    = STmVar (substVar x y v)

        substVar :: Var -> Var -> Var -> Var
        substVar x y v
          | v==x      = y
          | otherwise = v

test_flatten = flatten [Pos $ PApp "P" [TmApp "a" [], TmApp "f" [TmVar "x"]]]

{-
[Pos $ PApp "P" [TmApp "a" [], TmApp "f" [TmVar "x"]]]

P(a, f(x))

[Pos (SPApp "P" ["#0","#1"]),Neg (SEq (STmApp "a" []) "#0"),Neg (SEq (STmApp "f" ["x"]) "#1")]

f(x) ≠ z ∨ a ≠ y ∨ P(y,z)
(f(x) = z ∧ a = y) → P(y,z)
-}

-- ---------------------------------------------------------------------------

type Entity = Int

showEntity :: Entity -> String
showEntity e = "$" ++ show e

showEntityTuple :: [Entity] -> String
showEntityTuple xs = printf "(%s)" $ intercalate ", " $ map showEntity xs

-- ---------------------------------------------------------------------------

type GroundTerm   = SGenTerm Entity
type GroundAtom   = SGenAtom Entity
type GroundLit    = GenLit GroundAtom
type GroundClause = [GroundLit]

type Subst = Map.Map Var Entity

enumSubst :: Set.Set Var -> [Entity] -> [Subst]
enumSubst vs univ = do
  ps <- sequence [[(v,e) | e <- univ] | v <- Set.toList vs]
  return $ Map.fromList ps

applySubst :: Subst -> SClause -> GroundClause
applySubst s = map substLit
  where
    substLit :: SLit -> GroundLit
    substLit (Pos a) = Pos $ substAtom a
    substLit (Neg a) = Neg $ substAtom a

    substAtom :: SAtom -> GroundAtom
    substAtom (SPApp p xs) = SPApp p (map substVar xs)
    substAtom (SEq t v)    = SEq (substTerm t) (substVar v)

    substTerm :: STerm ->  GroundTerm
    substTerm (STmApp f xs) = STmApp f (map substVar xs)
    substTerm (STmVar v)    = STmVar (substVar v)

    substVar :: Var -> Entity
    substVar = (s Map.!)

simplifyGroundClause :: GroundClause -> Maybe GroundClause
simplifyGroundClause = liftM concat . mapM f
  where
    f :: GroundLit -> Maybe [GroundLit]
    f (Pos (SEq (STmVar x) y)) = if x==y then Nothing else return []
    f lit = return [lit]

collectFSym :: SClause -> Set.Set (FSym, Int)
collectFSym = Set.unions . map f
  where
    f :: SLit -> Set.Set (FSym, Int)
    f (Pos a) = g a
    f (Neg a) = g a

    g :: SAtom -> Set.Set (FSym, Int)
    g (SEq (STmApp f xs) _) = Set.singleton (f, length xs)
    g _ = Set.empty

collectPSym :: SClause -> Set.Set (PSym, Int)
collectPSym = Set.unions . map f
  where
    f :: SLit -> Set.Set (PSym, Int)
    f (Pos a) = g a
    f (Neg a) = g a

    g :: SAtom -> Set.Set (PSym, Int)
    g (SPApp p xs) = Set.singleton (p, length xs)
    g _ = Set.empty

-- ---------------------------------------------------------------------------

data Model
  = Model
  { mUniverse  :: [Entity]
  , mRelations :: Map.Map PSym [[Entity]]
  , mFunctions :: Map.Map FSym [([Entity], Entity)]
  }

showModel :: Model -> String
showModel m = 
  printf "DOMAIN = {%s}\n" (intercalate ", " (map showEntity (mUniverse m))) ++
  concat [ printf "%s = { %s }\n" p s
         | (p, xss) <- Map.toList (mRelations m)
         , let s = intercalate ", " [showEntityTuple xs | xs <- xss]
         ] ++
  concat [ printf "%s%s = %s\n" f (showEntityTuple xs) (showEntity y)
         | (f, xss) <- Map.toList (mFunctions m)
         , (xs, y) <- xss
         ]

-- ---------------------------------------------------------------------------

findModel :: Int -> [Clause] -> IO (Maybe Model)
findModel size cs = do
  let univ = [0..size-1]

  let cs2 = map flatten cs
      fs = Set.unions $ map collectFSym cs2
      ps = Set.unions $ map collectPSym cs2

  solver <- SAT.newSolver

  ref <- newIORef Map.empty

  let translateAtom :: GroundAtom -> IO SAT.Var
      translateAtom (SEq (STmVar _) _) = error "should not happen"
      translateAtom a = do
        m <- readIORef ref
        case Map.lookup a m of
          Just b  -> return b
          Nothing -> do
            b <- SAT.newVar solver
            writeIORef ref (Map.insert a b m)
            return b

      translateLit :: GroundLit -> IO SAT.Lit
      translateLit (Pos a) = translateAtom a
      translateLit (Neg a) = liftM negate $ translateAtom a

      translateClause :: GroundClause -> IO SAT.Clause
      translateClause = mapM translateLit

  -- Instances
  forM_ cs2 $ \c -> do
    forM_ (enumSubst (vars c) univ) $ \s -> do
      case simplifyGroundClause (applySubst s c) of
        Nothing -> return ()
        Just c' -> SAT.addClause solver =<< translateClause c'

  -- Functional definitions
  forM_ (Set.toList fs) $ \(f, arity) -> do
    forM_ (replicateM arity univ) $ \args ->
      forM_ [(y1,y2) | y1 <- univ, y2 <- univ, y1 < y2] $ \(y1,y2) -> do
        let c = [Neg (SEq (STmApp f args) y1), Neg (SEq (STmApp f args) y2)]
        c' <- translateClause c
        SAT.addClause solver c'

  -- Totality definitions
  forM_ (Set.toList fs) $ \(f, arity) -> do
    forM_ (replicateM arity univ) $ \args -> do
        let c = [Pos (SEq (STmApp f args) y) | y <- univ]
        c' <- translateClause c
        SAT.addClause solver c'

  ret <- SAT.solve solver
  if ret
    then do
      bmodel <- SAT.model solver
      m <- readIORef ref

      let rels = Map.fromList $ do
            (p,_) <- Set.toList ps
            let tbl = sort [xs | (SPApp p' xs, b) <- Map.toList m, p == p', bmodel ! b]
            return (p, tbl)
      let funs = Map.fromList $ do
            (f,_) <- Set.toList fs
            let tbl = sort [(xs, y) | (SEq (STmApp f' xs) y, b) <- Map.toList m, f == f', bmodel ! b]
            return (f, tbl)

      let model = Model
            { mUniverse  = univ
            , mRelations = rels
            , mFunctions = funs
            }

      return (Just model)
    else do
      return Nothing

-- ---------------------------------------------------------------------------

{-
∀x. ∃y. x≠y && f(y)=x
∀x. x≠g(x) ∧ f(g(x))=x
-}

test = do
  let c1 = [Pos $ PApp "=" [TmApp "f" [TmApp "g" [TmVar "x"]], TmVar "x"]]
      c2 = [Neg $ PApp "=" [TmVar "x", TmApp "g" [TmVar "x"]]]
  ret <- findModel 3 [c1, c2]
  case ret of
    Nothing -> putStrLn "=== NO MODEL FOUND ==="
    Just m -> do
      putStrLn "=== A MODEL FOUND ==="
      putStr $ showModel m

-- ---------------------------------------------------------------------------
