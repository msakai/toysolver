{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Arith.OmegaTest.Core
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- (incomplete) implementation of Omega Test
--
-- References:
--
-- * William Pugh. The Omega test: a fast and practical integer
--   programming algorithm for dependence analysis. In Proceedings of
--   the 1991 ACM/IEEE conference on Supercomputing (1991), pp. 4-13.
--
-- * <http://users.cecs.anu.edu.au/~michaeln/pubs/arithmetic-dps.pdf>
--
-- See also:
--
-- * <http://hackage.haskell.org/package/Omega>
--
-----------------------------------------------------------------------------
module ToySolver.Arith.OmegaTest.Core
    ( Model
    , solve
    , solveQFLA
    , Options (..)
    , defaultOptions
    , checkRealNoCheck
    , checkRealByFM

    -- * Exported just for testing
    , zmod
    ) where

import Control.Exception (assert)
import Control.Monad
import Data.Default.Class
import Data.List
import Data.Maybe
import Data.Ord
import Data.Ratio
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.VectorSpace

import ToySolver.Data.ArithRel
import ToySolver.Data.Boolean
import ToySolver.Data.DNF
import qualified ToySolver.Data.LA as LA
import ToySolver.Data.Var
import ToySolver.Internal.Util (combineMaybe)
import qualified ToySolver.Arith.FourierMotzkin as FM
import ToySolver.Arith.FourierMotzkin.Core (Constr (..), toLAAtom)

-- ---------------------------------------------------------------------------

data Options
  = Options
  { optCheckReal :: VarSet -> [LA.Atom Rational] -> Bool
  }

instance Default Options where
  def = defaultOptions

defaultOptions :: Options
defaultOptions =
  Options
  { optCheckReal =
      -- checkRealNoCheck
      checkRealByFM
  }

checkRealNoCheck :: VarSet -> [LA.Atom Rational] -> Bool
checkRealNoCheck _ _ = True

checkRealByFM :: VarSet -> [LA.Atom Rational] -> Bool
checkRealByFM vs as = isJust $ FM.solve vs as

-- ---------------------------------------------------------------------------

type ExprZ = LA.Expr Integer

-- 制約集合の単純化
-- It returns Nothing when a inconsistency is detected.
simplify :: [Constr] -> Maybe [Constr]
simplify = fmap concat . mapM f
  where
    f :: Constr -> Maybe [Constr]
    f (IsPos e) = f (IsNonneg (e ^-^ LA.constant 1))
    f constr@(IsNonneg e) =
      case LA.asConst e of
        Just x -> guard (x >= 0) >> return []
        Nothing -> return [constr]
    f constr@(IsZero e) =
      case LA.asConst e of
        Just x -> guard (x == 0) >> return []
        Nothing -> return [constr]

leZ, ltZ, geZ, gtZ, eqZ :: ExprZ -> ExprZ -> Constr
-- Note that constants may be floored by division
leZ e1 e2 = IsNonneg (LA.mapCoeff (`div` d) e)
  where
    e = e2 ^-^ e1
    d = abs $ gcd' [c | (c,v) <- LA.terms e, v /= LA.unitVar]
ltZ e1 e2 = (e1 ^+^ LA.constant 1) `leZ` e2
geZ = flip leZ
gtZ = flip ltZ
eqZ e1 e2 =
  case isZero (e1 ^-^ e2) of
    Just c -> c
    Nothing -> IsZero (LA.constant 1) -- unsatisfiable

isZero :: ExprZ -> Maybe Constr
isZero e
  = if LA.coeff LA.unitVar e `mod` d == 0
    then Just $ IsZero $ LA.mapCoeff (`div` d) e
    else Nothing
  where
    d = abs $ gcd' [c | (c,v) <- LA.terms e, v /= LA.unitVar]

applySubst1Constr :: Var -> ExprZ -> Constr -> Constr
applySubst1Constr v e (IsPos e2)    = LA.applySubst1 v e e2 `gtZ` LA.constant 0
applySubst1Constr v e (IsNonneg e2) = LA.applySubst1 v e e2 `geZ` LA.constant 0
applySubst1Constr v e (IsZero e2)   = LA.applySubst1 v e e2 `eqZ` LA.constant 0

evalConstr :: Model Integer -> Constr -> Bool
evalConstr m (IsPos t)    = LA.evalExpr m t > 0
evalConstr m (IsNonneg t) = LA.evalExpr m t >= 0
evalConstr m (IsZero t)   = LA.evalExpr m t == 0

-- ---------------------------------------------------------------------------

-- | (t,c) represents t/c, and c must be >0.
type Rat = (ExprZ, Integer)

{-
(ls,us) represents
{ x | ∀(M,c)∈ls. M/c≤x, ∀(M,c)∈us. x≤M/c }
-}
type BoundsZ = ([Rat],[Rat])

evalBoundsZ :: Model Integer -> BoundsZ -> IntervalZ
evalBoundsZ model (ls,us) =
  foldl' intersectZ univZ $ 
    [ (Just (ceiling (LA.evalExpr model x % c)), Nothing) | (x,c) <- ls ] ++ 
    [ (Nothing, Just (floor (LA.evalExpr model x % c))) | (x,c) <- us ]

collectBoundsZ :: Var -> [Constr] -> (BoundsZ, [Constr])
collectBoundsZ v = foldr phi (([],[]),[])
  where
    phi :: Constr -> (BoundsZ,[Constr]) -> (BoundsZ,[Constr])
    phi (IsPos t) x = phi (IsNonneg (t ^-^ LA.constant 1)) x
    phi constr@(IsNonneg t) ((ls,us),xs) =
      case LA.extract v t of
        (c,t') -> 
          case c `compare` 0 of
            EQ -> ((ls, us), constr : xs)
            GT -> (((negateV t', c) : ls, us), xs) -- 0 ≤ cx + M ⇔ -M/c ≤ x
            LT -> ((ls, (t', negate c) : us), xs)   -- 0 ≤ cx + M ⇔ x ≤ M/-c
    phi constr@(IsZero _) (bnd,xs) = (bnd, constr : xs) -- we assume v does not appear in constr

-- ---------------------------------------------------------------------------

solve' :: Options -> VarSet -> [Constr] -> Maybe (Model Integer)
solve' opt vs2 xs = simplify xs >>= go vs2
  where
    go :: VarSet -> [Constr] -> Maybe (Model Integer)
    go vs cs | IS.null vs = do
      let m = IM.empty
      guard $ all (evalConstr m) cs
      return m
    go vs cs | Just (e,cs2) <- extractEq cs = do
      (vs',cs3, mt) <- eliminateEq e vs cs2
      m <- go vs' =<< simplify cs3
      return (mt m)
    go vs cs = do
      guard $ optCheckReal opt vs (map toLAAtom cs)
      if isExact bnd then
        case1
      else
        case1 `mplus` case2

      where
        (v,vs',bnd@(ls,us),rest) = chooseVariable vs cs

        case1 = do
          let zs = [ LA.constant ((a-1)*(b-1)) `leZ` (a *^ d ^-^ b *^ c)
                   | (c,a)<-ls , (d,b)<-us ]
          model <- go vs' =<< simplify (zs ++ rest)
          case pickupZ (evalBoundsZ model bnd) of
            Nothing  -> error "ToySolver.OmegaTest.solve': should not happen"
            Just val -> return $ IM.insert v val model

        case2 = msum
          [ do c <- isZero $ a' *^ LA.var v ^-^ (c' ^+^ LA.constant k)
               model <- go vs (c : cs)
               return model
          | let m = maximum [b | (_,b)<-us]
          , (c',a') <- ls
          , k <- [0 .. (m*a'-a'-m) `div` m]
          ]

isExact :: BoundsZ -> Bool
isExact (ls,us) = and [a==1 || b==1 | (_,a)<-ls , (_,b)<-us]

chooseVariable :: VarSet -> [Constr] -> (Var, VarSet, BoundsZ, [Constr])
chooseVariable vs xs = head $ [e | e@(_,_,bnd,_) <- table, isExact bnd] ++ table
  where
    table = [ (v, IS.fromAscList vs', bnd, rest)
            | (v,vs') <- pickup (IS.toAscList vs), let (bnd, rest) = collectBoundsZ v xs
            ]

-- Find an equality constraint (e==0) and extract e with rest of constraints.
extractEq :: [Constr] -> Maybe (ExprZ, [Constr])
extractEq = msum . map f . pickup
  where
    f :: (Constr, [Constr]) -> Maybe (ExprZ, [Constr])
    f (IsZero e, ls) = Just (e, ls)
    f _ = Nothing

-- Eliminate an equality equality constraint (e==0).
eliminateEq :: ExprZ -> VarSet -> [Constr] -> Maybe (VarSet, [Constr], Model Integer -> Model Integer)
eliminateEq e vs cs | Just c <- LA.asConst e = guard (c==0) >> return (vs, cs, id)
eliminateEq e vs cs = do
  let (ak,xk) = minimumBy (comparing (abs . fst)) [(a,x) | (a,x) <- LA.terms e, x /= LA.unitVar]
  if abs ak == 1 then
    case LA.extract xk e of
      (_, e') -> do
        let xk_def = signum ak *^ negateV e'
        return $
           ( IS.delete xk vs
           , [applySubst1Constr xk xk_def c | c <- cs]
           , \model -> IM.insert xk (LA.evalExpr model xk_def) model
           )
  else do
    let m = abs ak + 1
    assert (ak `zmod` m == - signum ak) $ return ()
    let -- sigma is a fresh variable
        sigma = if IS.null vs then 0 else IS.findMax vs + 1
        -- m *^ LA.var sigma == LA.fromTerms [(a `zmod` m, x) | (a,x) <- LA.terms e]
        -- m *^ LA.var sigma == LA.fromTerms [(a `zmod` m, x) | (a,x) <- LA.terms e, x /= xk] ^+^ (ak `zmod` m) *^ LA.var xk
        -- m *^ LA.var sigma == LA.fromTerms [(a `zmod` m, x) | (a,x) <- LA.terms e, x /= xk] ^+^ (- signum ak) *^ LA.var xk
        -- LA.var xk == (- signum ak * m) *^ LA.var sigma ^+^ LA.fromTerms [(signum ak * (a `zmod` m), x) | (a,x) <- LA.terms e, x /= xk]
        xk_def = (- signum ak * m) *^ LA.var sigma ^+^
                   LA.fromTerms [(signum ak * (a `zmod` m), x) | (a,x) <- LA.terms e, x /= xk]
        -- e2 is normalized version of (LA.applySubst1 xk xk_def e).
        e2 = (- abs ak) *^ LA.var sigma ^+^ 
                LA.fromTerms [((floor (a%m + 1/2) + (a `zmod` m)), x) | (a,x) <- LA.terms e, x /= xk]
    assert (m *^ e2 == LA.applySubst1 xk xk_def e) $ return ()
    let mt model = IM.delete sigma $ IM.insert xk (LA.evalExpr model xk_def) model
    c <- isZero e2
    return (IS.insert sigma (IS.delete xk vs), c : [applySubst1Constr xk xk_def c | c <- cs], mt)

-- ---------------------------------------------------------------------------

type IntervalZ = (Maybe Integer, Maybe Integer)

univZ :: IntervalZ
univZ = (Nothing, Nothing)

intersectZ :: IntervalZ -> IntervalZ -> IntervalZ
intersectZ (l1,u1) (l2,u2) = (combineMaybe max l1 l2, combineMaybe min u1 u2)

pickupZ :: IntervalZ -> Maybe Integer
pickupZ (Nothing,Nothing) = return 0
pickupZ (Just x, Nothing) = return x
pickupZ (Nothing, Just x) = return x
pickupZ (Just x, Just y) = if x <= y then return x else mzero 

-- ---------------------------------------------------------------------------

solve :: Options -> VarSet -> [LA.Atom Rational] -> Maybe (Model Integer)
solve opt vs cs = msum [solve' opt vs cs | cs <- unDNF dnf]
  where
    dnf = andB (map f cs)
    f (ArithRel lhs op rhs) =
      case op of
        Lt  -> DNF [[a `ltZ` b]]
        Le  -> DNF [[a `leZ` b]]
        Gt  -> DNF [[a `gtZ` b]]
        Ge  -> DNF [[a `geZ` b]]
        Eql -> DNF [[a `eqZ` b]]
        NEq -> DNF [[a `ltZ` b], [a `gtZ` b]]
      where
        (e1,c1) = g lhs
        (e2,c2) = g rhs
        a = c2 *^ e1
        b = c1 *^ e2
    g :: LA.Expr Rational -> (ExprZ, Integer)
    g a = (LA.mapCoeff (\c -> floor (c * fromInteger d)) a, d)
      where
        d = foldl' lcm 1 [denominator c | (c,_) <- LA.terms a]

solveQFLA :: Options -> VarSet -> [LA.Atom Rational] -> VarSet -> Maybe (Model Rational)
solveQFLA opt vs cs ivs = listToMaybe $ do
  (cs2, mt) <- FM.projectN rvs cs
  m <- maybeToList $ solve opt ivs cs2
  return $ mt $ IM.map fromInteger m
  where
    rvs = vs `IS.difference` ivs

-- ---------------------------------------------------------------------------

zmod :: Integer -> Integer -> Integer
a `zmod` b = a - b * floor (a % b + 1 / 2)

gcd' :: [Integer] -> Integer
gcd' [] = 1
gcd' xs = foldl1' gcd xs

pickup :: [a] -> [(a,[a])]
pickup [] = []
pickup (x:xs) = (x,xs) : [(y,x:ys) | (y,ys) <- pickup xs]

-- ---------------------------------------------------------------------------
