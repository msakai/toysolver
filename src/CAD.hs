-----------------------------------------------------------------------------
-- |
-- Module      :  CAD
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
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

import Data.List
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

type P = UPolynomial Rational

data EndPoint = NegInf | RootOf P | PosInf
  deriving (Eq, Ord, Show)

data Cell
  = Point EndPoint
  | Interval -- open interval between two consective points
  deriving (Eq, Ord, Show)

data Sign = Neg | Zero | Pos
  deriving (Eq, Ord, Show)

type SignConf = [(Cell, Map.Map P Sign)]

-- 解を取り出せるようにしたい
elim1 :: [(P, Sign)] -> Bool
elim1 cs = not $ null $ filter ok conf
  where
    conf = buildSignConf (map fst cs)
    ok (_, m) = and [m Map.! p == s | (p,s) <- cs]

buildSignConf :: [P] -> SignConf
buildSignConf ps = foldl' (flip refineSignConf) emptySignConf ts
  where
    ps2 = collectPolynomials (Set.fromList ps)
    ts = sortBy (comparing deg) (Set.toList ps2)

collectPolynomials :: (Fractional r, Ord r) => Set.Set (UPolynomial r) -> Set.Set (UPolynomial r)
collectPolynomials ps = go ps ps
  where
    go qs ps | Set.null qs = ps
    go qs ps = go qs' ps'
      where
       rs = Set.fromList [deriv p () | p <- Set.toList qs] `Set.union`
            Set.fromList [p1 `polyMod` p2 | p1 <- Set.toList qs, p2 <- Set.toList qs, deg p1 >= deg p2, p2 /= 0]
       qs' = rs `Set.difference` ps
       ps' = ps `Set.union` qs'

showSignConf :: SignConf -> [String]
showSignConf = f
  where
    f :: SignConf -> [String]
    f [] = []
    f [(Point pt, m)] = showPt pt : g m
    f ((Point lb, m1) : (Interval, m2) : xs@((Point ub, _) : _)) =
      showPt lb : g m1 ++
      showInterval lb ub : g m2 ++
      f xs

    g :: Map.Map P Sign -> [String]
    g m =
      [printf "  %s: %s" (render p) (showSign s) | (p, s) <- Map.toList m]

    showPt :: EndPoint -> String
    showPt NegInf = "-inf" 
    showPt PosInf = "+inf"
    showPt (RootOf p) = "rootOf(" ++ render p ++ ")"

    showInterval :: EndPoint -> EndPoint -> String
    showInterval lb ub = printf "(%s, %s)" (showPt lb) (showPt ub)

    showSign :: Sign -> String
    showSign Pos  = "+"
    showSign Neg  = "-"
    showSign Zero = "0"

emptySignConf :: SignConf
emptySignConf = [(Point NegInf, Map.empty), (Interval, Map.empty), (Point PosInf, Map.empty)]

refineSignConf :: P -> SignConf -> SignConf
refineSignConf p conf = 
  case deg p of
    0 -> conf
    _ -> result
  where
    result = extendIntervals $ map extendPoint conf
 
    extendPoint :: (Cell, Map.Map P Sign) -> (Cell, Map.Map P Sign)
    extendPoint (Point pt, m) = (Point pt, Map.insert p (signAt pt m) m)
    extendPoint x = x
 
    extendIntervals :: [(Cell, Map.Map P Sign)] -> [(Cell, Map.Map P Sign)]
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
 
    signAt :: EndPoint -> Map.Map P Sign -> Sign
    signAt PosInf m = if c > 0 then Pos else Neg
      where
        (c,_) = leadingTerm grlex p
    signAt NegInf m =
      if even (deg p)
        then if c > 0 then Pos else Neg
        else if c > 0 then Neg else Pos
      where
        (c,_) = leadingTerm grlex p
    signAt (RootOf q) m
      | deg r > 0 = m Map.! r
      | otherwise =
          case coeff mmOne r `compare` 0 of
            EQ -> Zero
            GT -> Pos
            LT -> Neg
      where
        r = p `polyMod` q

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
