{-# OPTIONS_GHC -Wall #-}
module ToySolver.Wang
  ( Formula
  , Sequent
  , isValid
  ) where

import Control.Monad (guard,msum)
import Data.List (intersect)
import Data.Maybe (isJust, listToMaybe)
import ToySolver.Data.BoolExpr

type Formula a = BoolExpr a
type Sequent x = ([Formula x], [Formula x])

isValid :: Eq x => Sequent x -> Bool
isValid = isJust . isValid'

isValid' :: Eq x => Sequent x -> Maybe ()
isValid' (l,r) =
    do xs <- listToMaybe $ msum $
         [ do let i = intersect l r
              guard $ not $ null i
              return []
         , do (Not p, r) <- pick r
              return [(p:l,r)]
         , do (Not p, l) <- pick l
              return [(l,p:r)]
         , do (Imply p q, r) <- pick r
              return [(p:l,q:r)]
         , do (Or ps, r) <- pick r
              return [(l,ps++r)]
         , do (And ps, l) <- pick l
              return [(ps++l,r)]
         , do (Or ps, l)  <- pick l
              return [(p:l,r) | p <- ps]
         , do (And ps, r) <- pick r
              return [(l,p:r) | p <- ps]
         , do (Imply p q, l) <- pick l
              return [(q:l,r), (l,p:r)]

         , do (Equiv p q, l) <- pick l
              return [(Imply p q : Imply q p : l, r)]
         , do (Equiv p q, r) <- pick r
              return [(l, Imply p q : Imply q p : r)]
         ]
       mapM_ isValid' xs
       return ()

pick :: [x] -> [(x,[x])]
pick []     = []
pick (x:xs) = (x,xs) : [(y,x:ys) | (y,ys) <- pick xs]
