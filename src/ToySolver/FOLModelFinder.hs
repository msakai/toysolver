{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.FOLModelFinder
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables)
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
module ToySolver.FOLModelFinder
  (
  -- * Formula types
    Var
  , FSym
  , PSym
  , GenLit (..)
  , Term (..)
  , Atom (..)
  , Lit
  , Clause
  , Formula
  , GenFormula (..)
  , toSkolemNF

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
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Text.Printf

import ToySolver.Data.Boolean
import qualified ToySolver.SAT as SAT

-- ---------------------------------------------------------------------------

-- | Variable
type Var = String

-- | Function Symbol
type FSym = String

-- | Predicate Symbol
type PSym = String

class Vars a where
  vars :: a -> Set Var

instance Vars a => Vars [a] where
  vars = Set.unions . map vars

-- | Generalized literal type parameterized by atom type
data GenLit a
  = Pos a
  | Neg a
  deriving (Show, Eq, Ord)

instance Complement (GenLit a) where
  notB (Pos a) = Neg a
  notB (Neg a) = Pos a

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

-- Formula type
type Formula = GenFormula Atom

-- Generalized formula parameterized by atom type
data GenFormula a
  = T
  | F
  | Atom a
  | And (GenFormula a) (GenFormula a)
  | Or (GenFormula a) (GenFormula a)
  | Not (GenFormula a)
  | Imply (GenFormula a) (GenFormula a)
  | Equiv (GenFormula a) (GenFormula a)
  | Forall Var (GenFormula a)
  | Exists Var (GenFormula a)
  deriving (Show, Eq, Ord)

instance MonotoneBoolean (GenFormula a) where
  true = T
  false = F
  (.&&.) = And
  (.||.) = Or

instance Complement (GenFormula a) where
  notB = Not

instance Boolean (GenFormula a) where
  (.=>.) = Imply
  (.<=>.) = Equiv

instance Vars a => Vars (GenFormula a) where
  vars T               = Set.empty
  vars F               = Set.empty
  vars (Atom a)        = vars a
  vars (And phi psi)   = vars phi `Set.union` vars psi
  vars (Or phi psi)    = vars phi `Set.union` vars psi
  vars (Not phi)       = vars phi
  vars (Imply phi psi) = vars phi `Set.union` vars psi
  vars (Equiv phi psi) = vars phi `Set.union` vars psi
  vars (Forall v phi)  = Set.delete v (vars phi)
  vars (Exists v phi)  = Set.delete v (vars phi)

toNNF :: Formula -> Formula
toNNF = f
  where 
    f (And phi psi)   = f phi .&&. f psi
    f (Or phi psi)    = f phi .||. f psi
    f (Not phi)       = g phi
    f (Imply phi psi) = g phi .||. f psi
    f (Equiv phi psi) = f ((phi .=>. psi) .&&.  (psi .=>. phi))
    f (Forall v phi)  = Forall v (f phi)
    f (Exists v phi)  = Exists v (f phi)
    f phi = phi

    g :: Formula -> Formula
    g T = F
    g F = T
    g (And phi psi)   = g phi .||. g psi
    g (Or phi psi)    = g phi .&&. g psi
    g (Not phi)       = f phi
    g (Imply phi psi) = f phi .&&. g psi
    g (Equiv phi psi) = g ((phi .=>. psi) .&&. (psi .=>. phi))
    g (Forall v phi)  = Exists v (g phi)
    g (Exists v phi)  = Forall v (g phi)
    g (Atom a)        = notB (Atom a)

-- | normalize a formula into a skolem normal form.
-- 
-- TODO:
-- 
-- * Tseitin encoding
toSkolemNF :: forall m. Monad m => (String -> Int -> m FSym) -> Formula -> m [Clause]
toSkolemNF skolem phi = f [] Map.empty (toNNF phi)
  where
    f :: [Var] -> Map Var Term -> Formula -> m [Clause]
    f _ _ T = return []
    f _ _ F = return [[]]
    f _ s (Atom a) = return [[Pos (substAtom s a)]]
    f _ s (Not (Atom a)) = return [[Neg (substAtom s a)]]
    f uvs s (And phi psi) = do
      phi' <- f uvs s phi
      psi' <- f uvs s psi
      return $ phi' ++ psi'
    f uvs s (Or phi psi) = do
      phi' <- f uvs s phi
      psi' <- f uvs s psi
      return $ [c1++c2 | c1 <- phi', c2 <- psi']
    f uvs s psi@(Forall v phi) = do
      let v' = gensym v (vars psi `Set.union` Set.fromList uvs)
      f (v' : uvs) (Map.insert v (TmVar v') s) phi
    f uvs s (Exists v phi) = do
      fsym <- skolem v (length uvs)
      f uvs (Map.insert v (TmApp fsym [TmVar v | v <- reverse uvs]) s) phi
    f _ _ _ = error "ToySolver.FOLModelFinder.toSkolemNF: should not happen"

    gensym :: String -> Set Var -> Var
    gensym template vs = head [name | name <- names, Set.notMember name vs]
      where
        names = template : [template ++ show n | n <-[1..]]

    substAtom :: Map Var Term -> Atom -> Atom
    substAtom s (PApp p ts) = PApp p (map (substTerm s) ts)

    substTerm :: Map Var Term -> Term -> Term
    substTerm s (TmVar v)    = fromMaybe (TmVar v) (Map.lookup v s)
    substTerm s (TmApp f ts) = TmApp f (map (substTerm s) ts)

test_toSkolemNF = do
  ref <- newIORef 0
  let skolem name _ = do
        n <- readIORef ref
        let fsym = name ++ "#" ++ show n
        writeIORef ref (n+1)
        return fsym

  -- ∀x. animal(a) → (∃y. heart(y) ∧ has(x,y))
  let phi = Forall "x" $
                Atom (PApp "animal" [TmVar "x"]) .=>.
                (Exists "y" $
                   Atom (PApp "heart" [TmVar "y"]) .&&.
                   Atom (PApp "has" [TmVar "x", TmVar "y"]))

  phi' <- toSkolemNF skolem phi

  print phi'
{-
[[Neg (PApp "animal" [TmVar "x"]),Pos (PApp "heart" [TmApp "y#0" [TmVar "x"]])],[Neg (PApp "animal" [TmVar "x"]),Pos (PApp "has" [TmVar "x",TmApp "y#0" [TmVar "x"]])]]

{¬animal(x) ∨ heart(y#1(x)), ¬animal(x) ∨ has(x1, y#0(x))}
-}

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

type M = State (Set Var, Int, [SLit])

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

-- | Element of model.
type Entity = Int

-- | print entity
showEntity :: Entity -> String
showEntity e = "$" ++ show e

showEntityTuple :: [Entity] -> String
showEntityTuple xs = printf "(%s)" $ intercalate ", " $ map showEntity xs

-- ---------------------------------------------------------------------------

type GroundTerm   = SGenTerm Entity
type GroundAtom   = SGenAtom Entity
type GroundLit    = GenLit GroundAtom
type GroundClause = [GroundLit]

type Subst = Map Var Entity

enumSubst :: Set Var -> [Entity] -> [Subst]
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

collectFSym :: SClause -> Set (FSym, Int)
collectFSym = Set.unions . map f
  where
    f :: SLit -> Set (FSym, Int)
    f (Pos a) = g a
    f (Neg a) = g a

    g :: SAtom -> Set (FSym, Int)
    g (SEq (STmApp f xs) _) = Set.singleton (f, length xs)
    g _ = Set.empty

collectPSym :: SClause -> Set (PSym, Int)
collectPSym = Set.unions . map f
  where
    f :: SLit -> Set (PSym, Int)
    f (Pos a) = g a
    f (Neg a) = g a

    g :: SAtom -> Set (PSym, Int)
    g (SPApp p xs) = Set.singleton (p, length xs)
    g _ = Set.empty

-- ---------------------------------------------------------------------------

data Model
  = Model
  { mUniverse  :: [Entity]
  , mRelations :: Map PSym [[Entity]]
  , mFunctions :: Map FSym [([Entity], Entity)]
  }

showModel :: Model -> [String]
showModel m = 
  printf "DOMAIN = {%s}" (intercalate ", " (map showEntity (mUniverse m))) :
  [ printf "%s = { %s }" p s
  | (p, xss) <- Map.toList (mRelations m)
  , let s = intercalate ", " [if length xs == 1 then showEntity (head xs) else showEntityTuple xs | xs <- xss]
  ] ++
  [ printf "%s%s = %s" f (if length xs == 0 then "" else showEntityTuple xs) (showEntity y)
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
      bmodel <- SAT.getModel solver
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
      mapM_ putStrLn $ showModel m

test2 = do
  let phi = Forall "x" $ Exists "y" $
              notB (Atom (PApp "=" [TmVar "x", TmVar "y"])) .&&.
              Atom (PApp "=" [TmApp "f" [TmVar "y"], TmVar "x"])

  ref <- newIORef 0
  let skolem name _ = do
        n <- readIORef ref
        let fsym = name ++ "#" ++ show n
        writeIORef ref (n+1)
        return fsym
  cs <- toSkolemNF skolem phi

  ret <- findModel 3 cs
  case ret of
    Nothing -> putStrLn "=== NO MODEL FOUND ==="
    Just m -> do
      putStrLn "=== A MODEL FOUND ==="
      mapM_ putStrLn $ showModel m

-- ---------------------------------------------------------------------------
