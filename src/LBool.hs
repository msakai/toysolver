-----------------------------------------------------------------------------
-- |
-- Module      :  LBool
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Lifted boolean type.
-- 
-----------------------------------------------------------------------------
module LBool
  ( LBool
  , lTrue
  , lFalse
  , lUndef
  , lnot
  , liftBool
  , unliftBool
  ) where

import Data.Int

-- | Lifted Bool type. It has three values 'lTrue', 'lFalse', 'lUndef'.
newtype LBool = LBool Int8 deriving Eq

-- | lifted true value
{-# INLINE lTrue #-}
lTrue :: LBool
lTrue = LBool 1

-- | lifted false value
{-# INLINE lFalse #-}
lFalse :: LBool
lFalse = LBool (-1)

-- | undefined truth value
{-# INLINE lUndef #-}
lUndef :: LBool
lUndef = LBool 0

-- |
-- @
--   lnot lTrue == lFalse
--   lnot lFalse == lTrue
--   lnot lUndef == lUndef
-- @
{-# INLINE lnot #-}
lnot :: LBool -> LBool
lnot x
  | x == lTrue  = lFalse
  | x == lFalse = lTrue
  | otherwise   = lUndef

-- |
-- @
--   liftBool True == lTrue
--   liftBool False == lFalse
-- @
{-# INLINE liftBool #-}
liftBool :: Bool -> LBool
liftBool True  = lTrue
liftBool False = lFalse

-- |
-- @
--   unliftBool lTrue == Just True
--   unliftBool lFalse == Just False
--   unliftBool lUndef == Nothing
-- @
{-# INLINE unliftBool #-}
unliftBool :: LBool -> Maybe Bool
unliftBool x
  | x == lTrue  = Just True
  | x == lFalse = Just False
  | otherwise   = Nothing

instance Show LBool where
  show x
    | x == lTrue  = "lTrue"
    | x == lFalse = "lFalse"
    | otherwise   = "lUndef"
