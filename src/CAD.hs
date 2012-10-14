{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  CAD
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables)
--
-- References:
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
module CAD where

import Control.Exception
import Control.Monad.State
import Data.List
import Data.Maybe
import Data.Ord
import qualified Data.Map as Map
import qualified Data.Set as Set
import Text.Printf

import Data.ArithRel
-- import Data.AlgebraicNumber hiding (deg)
import Data.Formula (DNF (..))
import Data.Polynomial

import Debug.Trace

-- ---------------------------------------------------------------------------

type P v = Polynomial Rational v

data EndPoint v = NegInf | RootOf (P v) | PosInf
  deriving (Eq, Ord, Show)

data Cell v
  = Point (EndPoint v)
  | Interval -- open interval between two consective points
  deriving (Eq, Ord, Show)

data Sign = Neg | Zero | Pos
  deriving (Eq, Ord, Show)

signNegate :: Sign -> Sign
signNegate Neg  = Pos
signNegate Zero = Zero
signNegate Pos  = Neg

signDiv :: Sign -> Sign -> Sign
signDiv s Pos  = s
signDiv s Zero = error "signDiv: division by zero"
signDiv s Neg  = signNegate s

signOfConst :: Rational -> Sign
signOfConst r =
  case r `compare` 0 of
    LT -> Neg
    EQ -> Zero
    GT -> Pos

type SignConf v = [(Cell v, Map.Map (P v) Sign)]

-- 解を取り出せるようにしたい
elim1 :: [(P (), Sign)] -> Bool
elim1 cs = not $ null $ filter ok conf
  where
    conf = buildSignConf (map fst cs)
    ok (_, m) = and [m Map.! p == s | (p,s) <- cs]

buildSignConf :: [P ()] -> SignConf ()
buildSignConf ps = foldl' (flip refineSignConf) emptySignConf ts
  where
    ps2 = collectPolynomials (Set.fromList ps)
    ts = sortBy (comparing deg) (Set.toList ps2)

collectPolynomials :: (Fractional r, Ord r) => Set.Set (UPolynomial r) -> Set.Set (UPolynomial r)
collectPolynomials ps = go ps1 ps1
  where
    ps1 = f ps

    f :: Set.Set (Polynomial r v) -> Set.Set (Polynomial r v)
    f = Set.filter (\p -> deg p > 0)

    go qs ps | Set.null qs = ps
    go qs ps = go qs' ps'
      where
       rs = f $ Set.unions $
             [ Set.fromList [deriv p () | p <- Set.toList qs]
             , Set.fromList [p1 `polyMod` p2 | p1 <- Set.toList qs, p2 <- Set.toList ps, deg p1 >= deg p2, p2 /= 0]
             , Set.fromList [p1 `polyMod` p2 | p1 <- Set.toList ps, p2 <- Set.toList qs, deg p1 >= deg p2, p2 /= 0]
             ]
       qs' = rs `Set.difference` ps
       ps' = ps `Set.union` qs'

showSignConf :: forall v. (RenderVar v, Ord v) => SignConf v -> [String]
showSignConf = f
  where
    f :: SignConf v -> [String]
    f [] = []
    f [(Point pt, m)] = showPt pt : g m
    f ((Point lb, m1) : (Interval, m2) : xs@((Point ub, _) : _)) =
      showPt lb : g m1 ++
      showInterval lb ub : g m2 ++
      f xs

    g :: Map.Map (P v) Sign -> [String]
    g m =
      [printf "  %s: %s" (render p) (showSign s) | (p, s) <- Map.toList m]

    showPt :: EndPoint v -> String
    showPt NegInf = "-inf" 
    showPt PosInf = "+inf"
    showPt (RootOf p) = "rootOf(" ++ render p ++ ")"

    showInterval :: EndPoint v -> EndPoint v -> String
    showInterval lb ub = printf "(%s, %s)" (showPt lb) (showPt ub)

    showSign :: Sign -> String
    showSign Pos  = "+"
    showSign Neg  = "-"
    showSign Zero = "0"

emptySignConf :: SignConf v
emptySignConf = [(Point NegInf, Map.empty), (Interval, Map.empty), (Point PosInf, Map.empty)]

refineSignConf :: P () -> SignConf () -> SignConf ()
refineSignConf p conf = 
  case deg p of
    0 -> conf
    _ -> result
  where
    result = extendIntervals $ map extendPoint conf
 
    extendPoint :: (Cell (), Map.Map (P ()) Sign) -> (Cell (), Map.Map (P ()) Sign)
    extendPoint (Point pt, m) = (Point pt, Map.insert p (signAt pt m) m)
    extendPoint x = x
 
    extendIntervals :: [(Cell (), Map.Map (P ()) Sign)] -> [(Cell (), Map.Map (P ()) Sign)]
    extendIntervals (pt1@(Point _, m1) : (Interval, m) : pt2@(Point _, m2) : xs) =
      pt1 : ys ++ extendIntervals (pt2 : xs)
      where
        s1 = m1 Map.! p
        s2 = m2 Map.! p
        ys = if s1 == s2
             then [ (Interval, Map.insert p s1 m) ]
             else [ (Interval, Map.insert p s1 m)
                  , (Point (RootOf p), Map.insert p Zero m)
                  , (Interval, Map.insert p s2 m)
                  ]
    extendIntervals xs = xs
 
    signAt :: EndPoint () -> Map.Map (P ()) Sign -> Sign
    signAt PosInf _ = signCoeff c
      where
        (c,_) = leadingTerm grlex p
    signAt NegInf _ =
      if even (deg p)
        then signCoeff c
        else signNegate (signCoeff c)
      where
        (c,_) = leadingTerm grlex p
    signAt (RootOf q) m
      | deg r > 0 = m Map.! r
      | otherwise = signOfConst $ coeff mmOne r
      where
        r = p `polyMod` q

    signCoeff :: Rational -> Sign
    signCoeff = signOfConst

-- ---------------------------------------------------------------------------

test1a = mapM_ putStrLn $ showSignConf conf
  where
    x = var ()
    conf = buildSignConf [x + 1, -2*x + 3, x]

test1b = elim1 cs == True
  where
    x = var ()
    cs = [(x + 1, Pos), (-2*x + 3, Pos), (x, Pos)]

test2a = mapM_ putStrLn $ showSignConf conf
  where
    x = var ()
    conf = buildSignConf [x^2]

test2b = elim1 cs == False
  where
    x = var ()
    cs = [(x^2, Neg)]

test = and [test1b, test2b]

-- ---------------------------------------------------------------------------

type M v = StateT (Map.Map (P v) [Sign]) []

runM :: M v a -> [(a, Map.Map (P v) [Sign])]
runM m = runStateT m Map.empty

assume :: (Ord v, Show v, RenderVar v) => P v -> [Sign] -> M v ()
assume p ss =
  if deg p == 0
    then do
      let c = coeff mmOne p
      guard $ signOfConst c `elem` ss
    else do
      m <- get
      let ss1 = Map.findWithDefault [Neg, Zero, Pos] p m
          ss2 = intersect ss1 ss
      guard $ not $ null ss2
      put $ Map.insert p ss2 m

-- ---------------------------------------------------------------------------

elim2 :: [(P v, Sign)] -> v -> DNF (P v, Sign)
elim2 = undefined

buildSignConf2 :: (Ord v, Show v, RenderVar v) => v -> [P v] -> M v (SignConf v)
buildSignConf2 v ps = do
  ps2 <- collectPolynomials2 v (Set.fromList ps)
  let vDeg p = deg $ asPolynomialOf p v
      ts = sortBy (comparing vDeg) (Set.toList ps2)
  trace ("P = " ++ show [render p | p <- ts]) $ foldM (flip (refineSignConf2 v)) emptySignConf ts

collectPolynomials2
  :: (Ord v, Show v, RenderVar v)
  => v
  -> Set.Set (P v)
  -> M v (Set.Set (P v))
collectPolynomials2 v ps = do
  ps <- go (f ps)
  trace ("collect finished: " ++ show (map render (Set.toList ps))) $ return ()
  return ps
  where
    f = Set.filter (\p -> deg (asPolynomialOf p v) > 0) 

    go ps = do
      trace ("collect: " ++ show (map render (Set.toList ps))) $ return ()
      let rs1 = [deriv p v | p <- Set.toList ps]
      rs2 <- liftM (map (\(r, pd, qe) -> r) . catMaybes) $ 
        forM [(p1,p2) | p1 <- Set.toList ps, p2 <- Set.toList ps] $ \(p1,p2) -> do
          ret <- zmod v p1 p2
          trace (show (render p1, render p2, ret)) $ return ()
          return ret
      let ps' = f $ Set.unions [ps, Set.fromList rs1, Set.fromList rs2]
      if ps == ps'
        then return ps
        else go ps'

{-
P = ["0","2*x0",                                              "2*x0*x3 + x1","x0*x3^2 + x1*x3 + x2"]
P = ["0","2*x0","2*x0*x1","2*x0*x1^2",                        "2*x0*x3 + x1","x0*x3^2 + x1*x3 + x2"]
P = ["0","2*x0","2*x0*x1","2*x0*x1^2","2*x0*x1^3",            "2*x0*x3 + x1","x0*x3^2 + x1*x3 + x2"]
P = ["0","2*x0","2*x0*x1","2*x0*x1^2","2*x0*x1^3","2*x0*x1^4","2*x0*x3 + x1","x0*x3^2 + x1*x3 + x2"]

P = ["0","2*x0","2*x0*x1","2*x0*x1^2","2*x0*x1^3","2*x0*x1^4","2*x0*x1^5","2*x0*x3 + x1","x0*x3^2 + x1*x3 + x2"]
P = ["0","2*x0","2*x0*x1","2*x0*x1^2","2*x0*x1^3","2*x0*x1^4","2*x0*x1^5","2*x0*x1^6","2*x0*x3 + x1","x0*x3^2 + x1*x3 + x2"]
P = ["0","2*x0","2*x0*x1","2*x0*x1^2","2*x0*x1^3","2*x0*x1^4","2*x0*x1^5","2*x0*x1^6","2*x0*x1^7","2*x0*x3 + x1","x0*x3^2 + x1*x3 + x2"]

("2*x0*x3 + x1","2*x0",Just (fromTerms [(2 % 1,mmFromList [(0,1),(1,1)])],fromTerms [(2 % 1,mmFromList [(0,1)])],fromTerms [(2 % 1,mmFromList [(0,1)])]))

zmod "2*x0*x3 + x1" "2*x0" == (2*x0*x1, 2*x0, 2*x0)

(2*x0) * (2*x0*x3 + x1) - (2*x0) * x3 * (2*x0)
= 4*x0^2*x3 + 2*x0*x1 - 4*x0^2*x3
= 2*x0*x1

("2*x0*x3 + x1","2*x0*x1",Just (fromTerms [(2 % 1,mmFromList [(0,1),(1,2)])],fromTerms [(2 % 1,mmFromList [(0,1)])],fromTerms [(2 % 1,mmFromList [(0,1),(1,1)])]))

zmod "2*x0*x3 + x1" "2*x0*x1" == (2*x0*x1^2, 2*x0, 2*x0*x1)

(2*x0*x1) * (2*x0*x3 + x1) - (2*x0) * x3 * (2*x0*x1)
= 4*x0^2*x1*x3 * 2*x0*x1^2 - 4*x0^2*x1*x3
= 2*x0*x1^2
-}

-- TODO: 高次の項から見ていったほうが良い
getHighestNonzeroTerm :: (Ord v, Show v, RenderVar v) => UPolynomial (P v) -> M v (P v, Integer)
getHighestNonzeroTerm p = msum
    [ do forM_ [d+1 .. deg_p] $ \i -> assume (f i) [Zero]
         if (d >= 0)
           then do
             assume (f d) [Pos, Neg]
             return (f d, d)
           else do
             return (0, -1)
    | d <- [-1 .. deg_p]
    ]
  where
    deg_p = deg p
    f i = coeff (mmFromList [((), i)]) p

test_getHighestNonzeroTerm = runM (getHighestNonzeroTerm p')
  where
    p :: P Int
    a = var 0
    b = var 1
    c = var 2
    x = var 3
    p = a*x^2 +  b*x + c
    p' = asPolynomialOf p 3

zmod
  :: forall v. (Ord v, Show v, RenderVar v)
  => v
  -> P v
  -> P v
  -> M v (Maybe (P v, P v, P v))
zmod v p q = do
  let p' = asPolynomialOf p v
      q' = asPolynomialOf q v
  (pd, d) <- getHighestNonzeroTerm p'
  (qe, e) <- getHighestNonzeroTerm q'
  if d < e || qe == 0
    then return Nothing
    else do
      let p'' = sum [pi * (var v ^ mmDegree mm) | (pi, mm) <- terms p', mmDegree mm <= d]
          q'' = sum [qi * (var v ^ mmDegree mm) | (qi, mm) <- terms q', mmDegree mm <= e]
          result = qe * p'' - pd * (var v ^ (d-e)) * q''
          deg_result = deg (asPolynomialOf result v)
      assert (d <= 0 || deg_result < d) $ return $ Just $ (result, pd, qe)

-- ok
test_zmod = runM (zmod 0 p q)
  where
    p, q :: P Int
    x = var 0
    p = -2*x + 3
    q = x + 1

test_zmod2 =
  [ case ret of
      Just (p,pd,qe) -> show (render p, render pd, render qe, [(render p, ss) | (p,ss) <- Map.toList m])
      Nothing -> show [(render p, ss) | (p,ss) <- Map.toList m]
  | (ret,m) <- runM (zmod 3 p q)
  ]
  where
    p, q :: P Int
    a = var 0
    b = var 1
    c = var 2
    x = var 3
    p = a*x^2 + b*x + c
    q = 2*a*x + b

refineSignConf2 :: forall v. (Show v, Ord v, RenderVar v) => v -> P v -> SignConf v -> M v (SignConf v)
refineSignConf2 v p conf = do
  (_,d) <- getHighestNonzeroTerm p'
  if d <= 0
    then return conf
    else liftM extendIntervals $ mapM extendPoint conf

  where
    p' = asPolynomialOf p v
 
    extendPoint :: (Cell v, Map.Map (P v) Sign) -> M v (Cell v, Map.Map (P v) Sign)
    extendPoint (Point pt, m) = do
      s <- signAt pt m
      return (Point pt, Map.insert p s m)
    extendPoint x = return x
 
    extendIntervals :: [(Cell v, Map.Map (P v) Sign)] -> [(Cell v, Map.Map (P v) Sign)]
    extendIntervals (pt1@(Point _, m1) : (Interval, m) : pt2@(Point _, m2) : xs) =
      pt1 : ys ++ extendIntervals (pt2 : xs)
      where
        s1 = m1 Map.! p
        s2 = m2 Map.! p
        ys = if s1 == s2
             then [ (Interval, Map.insert p s1 m) ]
             else [ (Interval, Map.insert p s1 m)
                  , (Point (RootOf p), Map.insert p Zero m)
                  , (Interval, Map.insert p s2 m)
                  ]
    extendIntervals xs = xs
 
    signAt :: EndPoint v -> Map.Map (P v) Sign -> M v Sign
    signAt PosInf _ = do
      (c,_) <- getHighestNonzeroTerm p'
      signCoeff c
    signAt NegInf _ = do
      (c,d) <- getHighestNonzeroTerm p'
      if even d
        then signCoeff c
        else liftM signNegate $ signCoeff c
    signAt (RootOf q) m = do
      Just (r,_pd,qe) <- zmod v p q
      tbl <- get
      s1 <- if deg (asPolynomialOf r v) > 0
            then return $ m Map.! r
            else signCoeff r
      s2 <- signCoeff qe
      return $ signDiv s1 s2

    signCoeff :: P v -> M v Sign
    signCoeff c =
      msum [ assume c [s] >> return s
           | s <- [Neg, Zero, Pos]
           ]

asPolynomialOf :: (Eq k, Ord k, Num k, Ord v, Show v) => Polynomial k v -> v -> UPolynomial (Polynomial k v)
asPolynomialOf p v = fromTerms $ do
  (c,mm) <- terms p
  let m = mmToMap mm
  return ( fromTerms [(c, mmFromMap (Map.delete v m))]
         , mmFromList [((), Map.findWithDefault 0 v m)]
         )

-- ---------------------------------------------------------------------------


test_collectPolynomials2 = runM m
  where
    a = var 0
    b = var 1
    c = var 2
    x = var 3
    p :: P Int
    p = a*x^2 + b*x + c
    m = collectPolynomials2 3 (Set.singleton p)

test_collectPolynomials2b = do
  forM_ test_collectPolynomials2 $ \(ps,s) -> do
    putStrLn "============"
    mapM_ (putStrLn . render) (Set.toList ps)
    forM_  (Map.toList s) $ \(p, sign) ->
      printf "%s %s\n" (render p) (show sign)

test_buildSignConf2 = do
  forM_ cs $ \(conf, as) -> do
    putStrLn "============"
    mapM_ putStrLn $ showSignConf conf
    forM_  (Map.toList as) $ \(p, sign) ->
      printf "%s %s\n" (render p) (show sign)
  where
    a = var 0
    b = var 1
    c = var 2
    x = var 3
    p :: P Int
    p = a*x^2 + b*x + c

    cs :: [(SignConf Int, Map.Map (P Int) [Sign])]
    cs = runM (buildSignConf2 3 [p])

test_buildSignConf3 = do
  forM_ cs $ \(conf, as) -> do
    putStrLn "============"
    mapM_ putStrLn $ showSignConf conf
    forM_  (Map.toList as) $ \(p, sign) ->
      printf "%s %s\n" (render p) (show sign)
  where
    x = var 0
    ps :: [P Int]
    ps = [x + 1, -2*x + 3, x]

    cs :: [(SignConf Int, Map.Map (P Int) [Sign])]
    cs = runM (buildSignConf2 0 ps)

