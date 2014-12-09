{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Arith.OmegaTest
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
module ToySolver.Arith.OmegaTest
    ( Model
    , solve
    , solveQFLA
    , Options (..)
    , defaultOptions
    , checkRealNoCheck
    , checkRealByFM
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
import ToySolver.Arith.FourierMotzkin.Core (Lit (..), Rat, toLAAtom)

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
simplify :: [Lit] -> Maybe [Lit]
simplify = fmap concat . mapM f
  where
    f :: Lit -> Maybe [Lit]
    f lit@(Pos e) =
      case LA.asConst e of
        Just x -> guard (x > 0) >> return []
        Nothing -> return [lit]
    f lit@(Nonneg e) =
      case LA.asConst e of
        Just x -> guard (x >= 0) >> return []
        Nothing -> return [lit]

-- ---------------------------------------------------------------------------

leZ, ltZ, geZ, gtZ :: ExprZ -> ExprZ -> Lit
-- Note that constants may be floored by division
leZ e1 e2 = Nonneg (LA.mapCoeff (`div` d) e)
  where
    e = e2 ^-^ e1
    d = abs $ gcd' [c | (c,v) <- LA.terms e, v /= LA.unitVar]
ltZ e1 e2 = (e1 ^+^ LA.constant 1) `leZ` e2
geZ = flip leZ
gtZ = flip ltZ

eqZ :: ExprZ -> ExprZ -> (DNF Lit)
eqZ e1 e2
  = if LA.coeff LA.unitVar e3 `mod` d == 0
    then DNF [[Nonneg e, Nonneg (negateV e)]]
    else false
  where
    e = LA.mapCoeff (`div` d) e3
    e3 = e1 ^-^ e2
    d = abs $ gcd' [c | (c,v) <- LA.terms e3, v /= LA.unitVar]

-- ---------------------------------------------------------------------------

{-
(ls,us) represents
{ x | ∀(M,c)∈ls. M/c≤x, ∀(M,c)∈us. x≤M/c }
-}
type BoundsZ = ([Rat],[Rat])

collectBoundsZ :: Var -> [Lit] -> (BoundsZ,[Lit])
collectBoundsZ v = foldr phi (([],[]),[])
  where
    phi :: Lit -> (BoundsZ,[Lit]) -> (BoundsZ,[Lit])
    phi (Pos t) x = phi (Nonneg (t ^-^ LA.constant 1)) x
    phi lit@(Nonneg t) ((ls,us),xs) =
      case LA.extract v t of
        (c,t') -> 
          case c `compare` 0 of
            EQ -> ((ls, us), lit : xs)
            GT -> (((negateV t', c) : ls, us), xs) -- 0 ≤ cx + M ⇔ -M/c ≤ x
            LT -> ((ls, (t', negate c) : us), xs)   -- 0 ≤ cx + M ⇔ x ≤ M/-c

isExact :: BoundsZ -> Bool
isExact (ls,us) = and [a==1 || b==1 | (_,a)<-ls , (_,b)<-us]

solve' :: Options -> [Var] -> [Lit] -> Maybe (Model Integer)
solve' opt vs2 xs = simplify xs >>= go vs2
  where
    go :: [Var] -> [Lit] -> Maybe (Model Integer)
    go [] ys = do
      let m = IM.empty
      guard $ all (evalLit m) ys
      return m
    go vs ys = do
      guard $ optCheckReal opt (IS.fromList vs) (map toLAAtom ys)
      if isExact bnd then
        case1
      else
        case1 `mplus` case2

      where
        (v,vs',bnd@(ls,us),rest) = chooseVariable vs ys

        case1 = do
          let zs = [ LA.constant ((a-1)*(b-1)) `leZ` (a *^ d ^-^ b *^ c)
                   | (c,a)<-ls , (d,b)<-us ]
          model <- go vs' =<< simplify (zs ++ rest)
          case pickupZ (evalBoundsZ model bnd) of
            Nothing  -> error "ToySolver.OmegaTest.solve': should not happen"
            Just val -> return $ IM.insert v val model

        case2 = msum
          [ do eq <- isZero $ a' *^ LA.var v ^-^ (c' ^+^ LA.constant k)
               (vs'', lits'', mt) <- elimEq eq (v:vs') ys
               model <- go vs'' =<< simplify lits''
               return $ mt model
          | let m = maximum [b | (_,b)<-us]
          ,  (c',a') <- ls
          , k <- [0 .. (m*a'-a'-m) `div` m]
          ]

chooseVariable :: [Var] -> [Lit] -> (Var, [Var], BoundsZ, [Lit])
chooseVariable vs xs = head $ [e | e@(_,_,bnd,_) <- table, isExact bnd] ++ table
  where
    table = [ (v, vs', bnd, rest)
            | (v,vs') <- pickup vs, let (bnd, rest) = collectBoundsZ v xs
            ]

evalBoundsZ :: Model Integer -> BoundsZ -> IntervalZ
evalBoundsZ model (ls,us) =
  foldl' intersectZ univZ $ 
    [ (Just (ceiling (LA.evalExpr model x % c)), Nothing) | (x,c) <- ls ] ++ 
    [ (Nothing, Just (floor (LA.evalExpr model x % c))) | (x,c) <- us ]

-- Eliminate the equality (e == 0).
elimEq :: ExprZ -> [Var] -> [Lit] -> Maybe ([Var], [Lit], Model Integer -> Model Integer)
elimEq e vs lits = do
  let (ak,xk) = minimumBy (comparing (abs . fst)) [(a,x) | (a,x) <- LA.terms e, x /= LA.unitVar]
  if abs ak == 1 then
    case LA.extract xk e of
      (_, e') -> do
        let xk_def = signum ak *^ negateV e'
        return $
           ( vs
           , [applySubst1Lit xk xk_def lit | lit <- lits]
           , \model -> IM.insert xk (LA.evalExpr model xk_def) model
           )
  else do
    let m = abs ak + 1
    assert (ak `zmod` m == - signum ak) $ return ()
    let -- sigma is a fresh variable
        sigma = maximum (-1 : vs) + 1
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
    e3 <- isZero e2
    (vs2, lits2, mt) <- elimEq e3 (sigma : vs) [applySubst1Lit xk xk_def lit | lit <- lits]
    return $
        ( vs2
        , lits2
        , \model ->
             let model2 = mt model
             in IM.delete sigma $ IM.insert xk (LA.evalExpr model2 xk_def) model2
        )    

applySubst1Lit :: Var -> ExprZ -> Lit -> Lit
applySubst1Lit v e (Pos e2) = LA.applySubst1 v e e2 `gtZ` LA.constant 0
applySubst1Lit v e (Nonneg e2) = LA.applySubst1 v e e2 `geZ` LA.constant 0

evalLit :: Model Integer -> Lit -> Bool
evalLit m (Pos t) = LA.evalExpr m t > 0
evalLit m (Nonneg t) = LA.evalExpr m t >= 0

-- ---------------------------------------------------------------------------

isZero :: ExprZ -> Maybe ExprZ
isZero e
  = if LA.coeff LA.unitVar e `mod` d == 0
    then Just $ e2
    else Nothing
  where
    e2 = LA.mapCoeff (`div` d) e
    d = abs $ gcd' [c | (c,v) <- LA.terms e, v /= LA.unitVar]

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
solve opt vs cs = msum [solve' opt (IS.toList vs) lits | lits <- unDNF dnf]
  where
    dnf = andB (map f cs)
    f (ArithRel lhs op rhs) =
      case op of
        Lt  -> DNF [[a `ltZ` b]]
        Le  -> DNF [[a `leZ` b]]
        Gt  -> DNF [[a `gtZ` b]]
        Ge  -> DNF [[a `geZ` b]]
        Eql -> eqZ a b
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
