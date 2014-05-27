module ToySolver.Wang where

import Control.Monad (guard,msum)
import Data.List (intersect)
import Data.Maybe (isJust, listToMaybe)

data Formula x
    = Atom x
    | Not   !(Formula x)
    | Imply !(Formula x) !(Formula x)
    | And   !(Formula x) !(Formula x)
    | Or    !(Formula x) !(Formula x)
    deriving Eq

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
         , do (Or p q, r) <- pick r
              return [(l,p:q:r)]
         , do (And p q, l) <- pick l
              return [(p:q:l,r)]
         , do (Or p q, l)  <- pick l
              return [(p:l,r), (q:l,r)]
         , do (And p q, r) <- pick r
              return [(l,p:r), (l,q:r)]
         , do (Imply p q, l) <- pick l
              return [(q:l,r), (l,p:r)]
         ]
       mapM_ isValid' xs
       return ()

pick :: [x] -> [(x,[x])]
pick []     = []
pick (x:xs) = (x,xs) : [(y,x:ys) | (y,ys) <- pick xs]
