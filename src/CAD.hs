{-# LANGUAGE ScopedTypeVariables, BangPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  CAD
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables, BangPatterns)
--
-- References:
--
-- *  Christian Michaux and Adem Ozturk.
--    Quantifier Elimination following Muchnik
--    <https://math.umons.ac.be/preprints/src/Ozturk020411.pdf>
--
-- *  Arnab Bhattacharyya.
--    Something you should know about: Quantifier Elimination (Part I)
--    <http://cstheory.blogoverflow.com/2011/11/something-you-should-know-about-quantifier-elimination-part-i/>
-- 
-- *  Arnab Bhattacharyya.
--    Something you should know about: Quantifier Elimination (Part II)
--    <http://cstheory.blogoverflow.com/2012/02/something-you-should-know-about-quantifier-elimination-part-ii/>
--
-----------------------------------------------------------------------------
module CAD
  (
  -- * Basic data structures
    Point (..)
  , Cell (..)

  -- * Algebra os Sign
  , Sign (..)
  , signNegate
  , signMul
  , signDiv
  , signExp
  , signOfConst

  -- * Projection
  , project

  -- * Solving
  , solve
  , solve'

  -- * Model
  , Model
  , findSample
  , evalCell
  , evalPoint
  ) where

import Control.Exception
import Control.Monad.State
import Data.List
import Data.Maybe
import Data.Ord
import qualified Data.Map as Map
import qualified Data.Set as Set
import Text.Printf

import Data.ArithRel
import qualified Data.AlgebraicNumber as AReal
import Data.Formula (DNF (..))
import Data.Polynomial

import Debug.Trace

-- ---------------------------------------------------------------------------

data Point c = NegInf | RootOf (UPolynomial c) Int | PosInf
  deriving (Eq, Ord, Show)

data Cell c
  = Point (Point c)
  | Interval (Point c) (Point c)
  deriving (Eq, Ord, Show)

showCell :: (Num c, Ord c, RenderCoeff c) => Cell c -> String
showCell (Point pt) = showPoint pt
showCell (Interval lb ub) = printf "(%s, %s)" (showPoint lb) (showPoint ub)

showPoint :: (Num c, Ord c, RenderCoeff c) => Point c -> String
showPoint NegInf = "-inf"
showPoint PosInf = "+inf"
showPoint (RootOf p n) = "rootOf(" ++ render p ++ ", " ++ show n ++ ")"

-- ---------------------------------------------------------------------------

data Sign = Neg | Zero | Pos
  deriving (Eq, Ord, Show)

signNegate :: Sign -> Sign
signNegate Neg  = Pos
signNegate Zero = Zero
signNegate Pos  = Neg

signMul :: Sign -> Sign -> Sign
signMul Pos s  = s
signMul s Pos  = s
signMul Neg s  = signNegate s
signMul s Neg  = signNegate s
signMul _ _    = Zero

signDiv :: Sign -> Sign -> Sign
signDiv s Pos  = s
signDiv _ Zero = error "signDiv: division by zero"
signDiv s Neg  = signNegate s

signExp :: Sign -> Integer -> Sign
signExp _ 0    = Pos
signExp Pos _  = Pos
signExp Zero _ = Zero
signExp Neg n  = if even n then Pos else Neg

signOfConst :: (Num a, Ord a) => a -> Sign
signOfConst r =
  case r `compare` 0 of
    LT -> Neg
    EQ -> Zero
    GT -> Pos

-- ---------------------------------------------------------------------------

type SignConf c = [(Cell c, Map.Map (UPolynomial c) Sign)]

emptySignConf :: SignConf c
emptySignConf =
  [ (Point NegInf, Map.empty)
  , (Interval NegInf PosInf, Map.empty)
  , (Point PosInf, Map.empty)
  ]

showSignConf :: forall c. (Num c, Ord c, RenderCoeff c) => SignConf c -> [String]
showSignConf = f
  where
    f :: SignConf c -> [String]
    f = concatMap $ \(cell, m) -> showCell cell : g m

    g :: Map.Map (UPolynomial c) Sign -> [String]
    g m =
      [printf "  %s: %s" (render p) (showSign s) | (p, s) <- Map.toList m]

    showSign :: Sign -> String
    showSign Pos  = "+"
    showSign Neg  = "-"
    showSign Zero = "0"

-- ---------------------------------------------------------------------------

-- modified reminder
mr
  :: forall k. (Ord k, Show k, Num k, RenderCoeff k)
  => UPolynomial k
  -> UPolynomial k
  -> (k, Integer, UPolynomial k)
mr p q
  | n >= m    = assert (constant (bm^(n-m+1)) * p == q * l + r && m > deg r) $ (bm, n-m+1, r)
  | otherwise = error "mr p q: not (deg p >= deg q)"
  where
    x = var ()
    n = deg p
    m = deg q
    (bm, _) = leadingTerm grlex q
    (l,r) = f p n

    f :: UPolynomial k -> Integer -> (UPolynomial k, UPolynomial k)
    f p n
      | n==m =
          let l = constant an
              r = constant bm * p - constant an * q
          in assert (constant (bm^(n-m+1)) * p == q*l + r && m > deg r) $ (l, r)
      | otherwise =
          let p'     = (constant bm * p - constant an * x^(n-m) * q)
              (l',r) = f p' (n-1)
              l      = l' + constant (an*bm^(n-m)) * x^(n-m)
          in assert (n > deg p') $
             assert (constant (bm^(n-m+1)) * p == q*l + r && m > deg r) $ (l, r)
      where
        an = coeff (mmFromList [((), n)]) p

test_mr_1 :: (Coeff Int, Integer, UPolynomial (Coeff Int))
test_mr_1 = mr (toUPolynomialOf p 3) (toUPolynomialOf q 3)
  where
    a = var 0
    b = var 1
    c = var 2
    x = var 3
    p = a*x^(2::Int) + b*x + c
    q = 2*a*x + b

test_mr_2 :: (Coeff Int, Integer, UPolynomial (Coeff Int))
test_mr_2 = mr (toUPolynomialOf p 3) (toUPolynomialOf p 3)
  where
    a = var 0
    b = var 1
    c = var 2
    x = var 3
    p = a*x^(2::Int) + b*x + c

-- ---------------------------------------------------------------------------

type Coeff v = Polynomial Rational v

type M v = StateT (Map.Map (Polynomial Rational v) (Set.Set Sign)) []

runM :: M v a -> [(a, Map.Map (Polynomial Rational v) (Set.Set Sign))]
runM m = runStateT m Map.empty

assume :: (Ord v, Show v, RenderVar v) => Polynomial Rational v -> [Sign] -> M v ()
assume p ss =
  if deg p == 0
    then do
      let c = coeff mmOne p
      guard $ signOfConst c `elem` ss
    else do      
      let (c,_) = leadingTerm grlex p
          p' = mapCoeff (/c) p
      m <- get
      let ss1 = Map.findWithDefault (Set.fromList [Neg, Zero, Pos]) p' m
          ss2 = Set.intersection ss1 $ Set.fromList $ [s `signDiv` signOfConst c | s <- ss]
      guard $ not $ Set.null ss2
      put $ Map.insert p' ss2 m

project
  :: forall v. (Ord v, Show v, RenderVar v)
  => [(UPolynomial (Polynomial Rational v), [Sign])]
  -> [([(Polynomial Rational v, [Sign])], [Cell (Polynomial Rational v)])]
project cs = [ (guess2cond gs, cells) | (cells, gs) <- result ]
  where
    result :: [([Cell (Polynomial Rational v)], Map.Map (Polynomial Rational v) (Set.Set Sign))]
    result = runM $ do
      forM_ cs $ \(p,ss) -> do
        when (1 > deg p) $ assume (coeff mmOne p) ss
      conf <- buildSignConf (map fst cs)
      let satCells = [cell | (cell, m) <- conf, cell /= Point NegInf, cell /= Point PosInf, ok m]
      guard $ not $ null satCells
      return satCells

    ok :: Map.Map (UPolynomial (Polynomial Rational v)) Sign -> Bool
    ok m = and [checkSign m p ss | (p,ss) <- cs]
      where
        checkSign m p ss =
          if 1 > deg p 
            then True -- already assumed
            else (m Map.! p) `elem` ss

    guess2cond :: Map.Map (Polynomial Rational v) (Set.Set Sign) -> [(Polynomial Rational v, [Sign])]
    guess2cond gs = [(p, Set.toList ss)  | (p, ss) <- Map.toList gs]

buildSignConf
  :: (Ord v, Show v, RenderVar v)
  => [UPolynomial (Polynomial Rational v)]
  -> M v (SignConf (Polynomial Rational v))
buildSignConf ps = do
  ps2 <- collectPolynomials (Set.fromList ps)
  let ts = sortBy (comparing deg) (Set.toList ps2)
  foldM (flip refineSignConf) emptySignConf ts

collectPolynomials
  :: (Ord v, Show v, RenderVar v)
  => Set.Set (UPolynomial (Polynomial Rational v))
  -> M v (Set.Set (UPolynomial (Polynomial Rational v)))
collectPolynomials ps = go Set.empty (f ps)
  where
    f = Set.filter (\p -> deg p > 0) 
    go result ps | Set.null ps = return result
    go result ps = do
      let rs1 = filter (\p -> deg p > 0) [deriv p () | p <- Set.toList ps]
      rs2 <- liftM (filter (\p -> deg p > 0) . map (\(_,_,r) -> r) . concat) $
        forM [(p1,p2) | p1 <- Set.toList ps, p2 <- Set.toList ps ++ Set.toList result, p1 /= p2] $ \(p1,p2) -> do
          ret1 <- zmod p1 p2
          ret2 <- zmod p2 p1
          return $ catMaybes [ret1,ret2]
      let ps' = Set.unions [Set.fromList rs | rs <- [rs1,rs2]] `Set.difference` result
      go (result `Set.union` ps) ps'

getHighestNonzeroTerm
  :: forall v. (Ord v, Show v, RenderVar v)
  => UPolynomial (Polynomial Rational v)
  -> M v (Polynomial Rational v, Integer)
getHighestNonzeroTerm p = go $ sortBy (flip (comparing snd)) cs
  where
    cs = [(c, mmDegree mm) | (c,mm) <- terms p]

    go :: [(Polynomial Rational v, Integer)] -> M v (Polynomial Rational v, Integer)
    go [] = return (0, -1)
    go ((c,d):xs) =
      mplus
        (assume c [Pos, Neg] >> return (c,d))
        (assume c [Zero] >> go xs)

zmod
  :: forall v. (Ord v, Show v, RenderVar v)
  => UPolynomial (Polynomial Rational v)
  -> UPolynomial (Polynomial Rational v)
  -> M v (Maybe (Polynomial Rational v, Integer, UPolynomial (Polynomial Rational v)))
zmod p q = do
  (_, d) <- getHighestNonzeroTerm p
  (_, e) <- getHighestNonzeroTerm q
  if not (d >= e) || 0 >= e
    then return Nothing
    else do
      let p' = fromTerms [(pi, mm) | (pi, mm) <- terms p, mmDegree mm <= d]
          q' = fromTerms [(qi, mm) | (qi, mm) <- terms q, mmDegree mm <= e]
      return $ Just $ mr p' q'

refineSignConf
  :: forall v. (Show v, Ord v, RenderVar v)
  => UPolynomial (Polynomial Rational v)
  -> SignConf (Polynomial Rational v) 
  -> M v (SignConf (Polynomial Rational v))
refineSignConf p conf = liftM (extendIntervals 0) $ mapM extendPoint conf
  where 
    extendPoint
      :: (Cell (Polynomial Rational v), Map.Map (UPolynomial (Polynomial Rational v)) Sign)
      -> M v (Cell (Polynomial Rational v), Map.Map (UPolynomial (Polynomial Rational v)) Sign)
    extendPoint (Point pt, m) = do
      s <- signAt pt m
      return (Point pt, Map.insert p s m)
    extendPoint x = return x
 
    extendIntervals
      :: Int
      -> [(Cell (Polynomial Rational v), Map.Map (UPolynomial (Polynomial Rational v)) Sign)]
      -> [(Cell (Polynomial Rational v), Map.Map (UPolynomial (Polynomial Rational v)) Sign)]
    extendIntervals !n (pt1@(Point _, m1) : (Interval lb ub, m) : pt2@(Point _, m2) : xs) =
      pt1 : ys ++ extendIntervals n2 (pt2 : xs)
      where
        s1 = m1 Map.! p
        s2 = m2 Map.! p
        n1 = if s1 == Zero then n+1 else n
        root = RootOf p n1
        (ys, n2)
           | s1 == s2   = ( [ (Interval lb ub, Map.insert p s1 m) ], n1 )
           | s1 == Zero = ( [ (Interval lb ub, Map.insert p s2 m) ], n1 )
           | s2 == Zero = ( [ (Interval lb ub, Map.insert p s1 m) ], n1 )
           | otherwise  = ( [ (Interval lb root, Map.insert p s1   m)
                            , (Point root,       Map.insert p Zero m)
                            , (Interval root ub, Map.insert p s2   m)
                            ]
                          , n1 + 1
                          )
    extendIntervals _ xs = xs
 
    signAt :: Point (Polynomial Rational v) -> Map.Map (UPolynomial (Polynomial Rational v)) Sign -> M v Sign
    signAt PosInf _ = do
      (c,_) <- getHighestNonzeroTerm p
      signCoeff c
    signAt NegInf _ = do
      (c,d) <- getHighestNonzeroTerm p
      if even d
        then signCoeff c
        else liftM signNegate $ signCoeff c
    signAt (RootOf q _) m = do
      Just (bm,k,r) <- zmod p q
      s1 <- if deg r > 0
            then return $ m Map.! r
            else signCoeff $ coeff mmOne r
      -- 場合分けを出来るだけ避ける
      if even k
        then return s1
        else do
          s2 <- signCoeff bm
          return $ signDiv s1 (signExp s2 k)

    signCoeff :: Polynomial Rational v -> M v Sign
    signCoeff c =
      msum [ assume c [s] >> return s
           | s <- [Neg, Zero, Pos]
           ]

-- ---------------------------------------------------------------------------

type Model v = Map.Map v AReal.AReal

findSample :: Ord v => Model v -> Cell (Polynomial Rational v) -> Maybe AReal.AReal
findSample m cell =
  case evalCell m cell of
    Point (RootOf p n) -> 
      Just $ AReal.realRoots p !! n
    Interval NegInf PosInf ->
      Just $ 0
    Interval NegInf (RootOf p n) ->
      Just $ fromInteger $ floor   ((AReal.realRoots p !! n) - 1)
    Interval (RootOf p n) PosInf ->
      Just $ fromInteger $ ceiling ((AReal.realRoots p !! n) + 1)
    Interval (RootOf p1 n1) (RootOf p2 n2)
      | (pt1 < pt2) -> Just $ (pt1 + pt2) / 2
      | otherwise   -> Nothing
      where
        pt1 = AReal.realRoots p1 !! n1
        pt2 = AReal.realRoots p2 !! n2
    _ -> error $ "findSample: should not happen"

evalCell :: Ord v => Model v -> Cell (Polynomial Rational v) -> Cell Rational
evalCell m (Point pt)         = Point $ evalPoint m pt
evalCell m (Interval pt1 pt2) = Interval (evalPoint m pt1) (evalPoint m pt2)

evalPoint :: Ord v => Model v -> Point (Polynomial Rational v) -> Point Rational
evalPoint _ NegInf = NegInf
evalPoint _ PosInf = PosInf
evalPoint m (RootOf p n) =
  RootOf (AReal.simpARealPoly $ mapCoeff (eval (m Map.!) . mapCoeff fromRational) p) n

-- ---------------------------------------------------------------------------

solve
  :: forall v. (Ord v, Show v, RenderVar v)
  => [(Rel (Polynomial Rational v))]
  -> Maybe (Model v)
solve cs0 = solve' (map f cs0)
  where
    f (Rel lhs op rhs) = (lhs - rhs, g op)
    g Le  = [Zero, Neg]
    g Ge  = [Zero, Pos]
    g Lt  = [Neg]
    g Gt  = [Pos]
    g Eql = [Zero]
    g NEq = [Pos,Neg]

solve'
  :: forall v. (Ord v, Show v, RenderVar v)
  => [(Polynomial Rational v, [Sign])]
  -> Maybe (Model v)
solve' cs0 = go vs0 cs0
  where
    vs0 = Set.toList $ Set.unions [variables p | (p,_) <- cs0]

    go :: [v] -> [(Polynomial Rational v, [Sign])] -> Maybe (Model v)
    go [] cs =
      if and [signOfConst v `elem` ss | (p,ss) <- cs, let v = eval (\_ -> undefined) p]
      then Just Map.empty
      else Nothing
    go (v:vs) cs = listToMaybe $ do
      (cs2, cell:_) <- project [(toUPolynomialOf p v, ss) | (p,ss) <- cs]
      case go vs cs2 of
        Nothing -> mzero
        Just m -> do
          let Just val = findSample m cell
          seq val $ return $ Map.insert v val m

-- ---------------------------------------------------------------------------

showDNF :: (Ord v, Show v, RenderVar v) => DNF (Polynomial Rational v, [Sign]) -> String
showDNF (DNF xss) = intercalate " | " [showConj xs | xs <- xss]
  where
    showConj xs = "(" ++ intercalate " & " [f p ss | (p,ss) <- xs] ++ ")"
    f p ss = render p ++ g ss
    g [Zero] = " = 0"
    g [Pos]  = " > 0"
    g [Neg]  = " < 0"
    g xs
      | Set.fromList xs == Set.fromList [Pos,Neg] = "/= 0"
      | Set.fromList xs == Set.fromList [Zero,Pos] = ">= 0"
      | Set.fromList xs == Set.fromList [Zero,Neg] = "<= 0"
      | otherwise = error "showDNF: should not happen"

dumpProjection
  :: (Ord v, Show v, RenderVar v)
  => [([(Polynomial Rational v, [Sign])], [Cell (Polynomial Rational v)])]
  -> IO ()
dumpProjection xs =
  forM_ xs $ \(gs, cells) -> do
    putStrLn "============"
    forM_ gs $ \(p, ss) -> do
      putStrLn $ f p ss
    putStrLn " =>"
    forM_ cells $ \cell -> do
      putStrLn $ showCell cell
  where
    f p ss = render p ++ g ss
    g [Zero] = " = 0"
    g [Pos]  = " > 0"
    g [Neg]  = " < 0"
    g xs
      | Set.fromList xs == Set.fromList [Pos,Neg]  = "/= 0"
      | Set.fromList xs == Set.fromList [Zero,Pos] = ">= 0"
      | Set.fromList xs == Set.fromList [Zero,Neg] = "<= 0"
      | otherwise = error "showDNF: should not happen"

dumpSignConf
  :: forall v.
     (Ord v, RenderVar v, Show v)
  => [(SignConf (Polynomial Rational v), Map.Map (Polynomial Rational v) (Set.Set Sign))]
  -> IO ()
dumpSignConf x = 
  forM_ x $ \(conf, as) -> do
    putStrLn "============"
    mapM_ putStrLn $ showSignConf conf
    forM_  (Map.toList as) $ \(p, sign) ->
      printf "%s %s\n" (render p) (show sign)

-- ---------------------------------------------------------------------------

test1a :: IO ()
test1a = mapM_ putStrLn $ showSignConf conf
  where
    x = var ()
    ps :: [UPolynomial (Polynomial Rational Int)]
    ps = [x + 1, -2*x + 3, x]
    [(conf, _)] = runM $ buildSignConf ps

test1b :: Bool
test1b = isJust $ solve cs
  where
    x = var ()
    cs = [x + 1 .>. 0, -2*x + 3 .>. 0, x .>. 0]

test1c :: Bool
test1c = isJust $ do
  m <- solve' cs
  guard $ and $ do
    (p, ss) <- cs
    let val = eval (m Map.!) (mapCoeff fromRational p)
    return $ signOfConst val `elem` ss
  where
    x = var ()
    cs = [(x + 1, [Pos]), (-2*x + 3, [Pos]), (x, [Pos])]

test2a :: IO ()
test2a = mapM_ putStrLn $ showSignConf conf
  where
    x = var ()
    ps :: [UPolynomial (Polynomial Rational Int)]
    ps = [x^(2::Int)]
    [(conf, _)] = runM $ buildSignConf ps

test2b :: Bool
test2b = isNothing $ solve cs
  where
    x = var ()
    cs = [x^(2::Int) .<. 0]

test = and [test1b, test1c, test2b]

test_project :: DNF (Polynomial Rational Int, [Sign])
test_project = DNF $ map fst $ project [(p', [Zero])]
  where
    a = var 0
    b = var 1
    c = var 2
    x = var 3
    p :: Polynomial Rational Int
    p = a*x^(2::Int) + b*x + c
    p' = toUPolynomialOf p 3

test_project_print :: IO ()
test_project_print = putStrLn $ showDNF $ test_project

test_project_2 = project [(p, [Zero]), (x, [Pos])]
  where
    x = var ()
    p :: UPolynomial (Polynomial Rational Int)
    p = x^(2::Int) + 4*x - 10

test_project_3_print =  dumpProjection $ project [(toUPolynomialOf p 0, [Neg])]
  where
    a = var 0
    b = var 1
    c = var 2
    p :: Polynomial Rational Int
    p = a^(2::Int) + b^(2::Int) + c^(2::Int) - 1

test_solve = solve [p .<. 0]
  where
    a = var 0
    b = var 1
    c = var 2
    p :: Polynomial Rational Int
    p = a^(2::Int) + b^(2::Int) + c^(2::Int) - 1

test_collectPolynomials
  :: [( Set.Set (UPolynomial (Polynomial Rational Int))
      , Map.Map (Polynomial Rational Int) (Set.Set Sign)
      )]
test_collectPolynomials = runM $ collectPolynomials (Set.singleton p')
  where
    a = var 0
    b = var 1
    c = var 2
    x = var 3
    p :: Polynomial Rational Int
    p = a*x^(2::Int) + b*x + c
    p' = toUPolynomialOf p 3

test_collectPolynomials_print :: IO ()
test_collectPolynomials_print = do
  forM_ test_collectPolynomials $ \(ps,s) -> do
    putStrLn "============"
    mapM_ (putStrLn . render) (Set.toList ps)
    forM_  (Map.toList s) $ \(p, sign) ->
      printf "%s %s\n" (render p) (show sign)

test_buildSignConf :: [(SignConf (Polynomial Rational Int), Map.Map (Polynomial Rational Int) (Set.Set Sign))]
test_buildSignConf = runM $ buildSignConf [toUPolynomialOf p 3]
  where
    a = var 0
    b = var 1
    c = var 2
    x = var 3
    p :: Polynomial Rational Int
    p = a*x^(2::Int) + b*x + c

test_buildSignConf_print :: IO ()
test_buildSignConf_print = dumpSignConf test_buildSignConf

test_buildSignConf_2 :: [(SignConf (Polynomial Rational Int), Map.Map (Polynomial Rational Int) (Set.Set Sign))]
test_buildSignConf_2 = runM $ buildSignConf [toUPolynomialOf p 0 | p <- ps]
  where
    x = var 0
    ps :: [Polynomial Rational Int]
    ps = [x + 1, -2*x + 3, x]

test_buildSignConf_2_print :: IO ()
test_buildSignConf_2_print = dumpSignConf test_buildSignConf_2

test_buildSignConf_3 :: [(SignConf (Polynomial Rational Int), Map.Map (Polynomial Rational Int) (Set.Set Sign))]
test_buildSignConf_3 = runM $ buildSignConf [toUPolynomialOf p 0 | p <- ps]
  where
    x = var 0
    ps :: [Polynomial Rational Int]
    ps = [x, 2*x]

test_buildSignConf_3_print :: IO ()
test_buildSignConf_3_print = dumpSignConf test_buildSignConf_3

-- ---------------------------------------------------------------------------
