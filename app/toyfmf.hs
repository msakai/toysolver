{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP, TypeFamilies, OverloadedStrings #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  toyfmf
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable (CPP, TypeFamilies, OverloadedStrings)
--
-- A toy-level model finder
--
-----------------------------------------------------------------------------
module Main where

import Control.Monad
import Data.Interned (intern, unintern)
import Data.IORef
import qualified Data.Map as Map
#if !MIN_VERSION_base(4,11,0)
import Data.Monoid
#endif
import Data.Ratio
import Data.String
import qualified Data.Text as Text
import Options.Applicative
import qualified Codec.TPTP as TPTP
import ToySolver.Data.Boolean
import qualified ToySolver.EUF.FiniteModelFinder as MF
import ToySolver.Internal.Util (setEncodingChar8)

data Options
  = Options
  { optInput :: FilePath
  , optSize :: Int
  }

optionsParser :: Parser Options
optionsParser = Options
  <$> fileInput
  <*> sizeInput
  where
    fileInput :: Parser FilePath
    fileInput = argument str $ metavar "FILE.tptp"

    sizeInput :: Parser Int
    sizeInput = argument auto $ metavar "SIZE"

parserInfo :: ParserInfo Options
parserInfo = info (helper <*> optionsParser)
  $  fullDesc
  <> header "toyfmf - a finite model finder"

main :: IO ()
main = do
#ifdef FORCE_CHAR8
  setEncodingChar8
#endif
  opt <- execParser parserInfo
  solve (optInput opt) (optSize opt)

solve :: FilePath -> Int -> IO ()
solve _ size | size <= 0 = error "<size> should be >=1"
solve fpath size = do
  inputs <- TPTP.parseFile fpath
  let fs = translateProblem inputs

  ref <- newIORef (0::Int)
  let skolem name _ = do
        n <- readIORef ref
        let fsym = intern $ unintern name <> "#" <> fromString (show n)
        writeIORef ref (n+1)
        return fsym
  cs <- liftM concat $ mapM (MF.toSkolemNF skolem) fs

  ret <- MF.findModel size cs
  case ret of
    Nothing -> do
      putStrLn "s NO MODEL FOUND"
    Just m -> do
      putStrLn "s SATISFIABLE"
      let isSkolem k = Text.any ('#'==) (unintern k)
      let m' = m{ MF.mFunctions = Map.filterWithKey (\k _ -> not (isSkolem k)) (MF.mFunctions m) }
      forM_ (MF.showModel m') $ \s ->
        putStrLn $ "v " ++ s

  return ()

-- ---------------------------------------------------------------------------

translateProblem :: [TPTP.TPTP_Input] -> [MF.Formula]
translateProblem inputs = do
  i <- inputs
  case i of
    TPTP.Comment _ -> []
    TPTP.Include _ _ -> error "\"include\" is not supported yet "
    TPTP.AFormula{ TPTP.name = _, TPTP.role = _, TPTP.formula = formula, TPTP.annotations = _ } ->
      return $ translateFormula formula

translateFormula :: TPTP.Formula -> MF.Formula
translateFormula = TPTP.foldF neg quant binop eq rel
  where
    neg phi = notB $ translateFormula phi
    quant q vs phi = foldr q' (translateFormula phi) [fromString v | TPTP.V v <- vs]
      where
        q' =
          case q of 
            TPTP.All    -> MF.Forall
            TPTP.Exists -> MF.Exists
    binop phi op psi = op' phi' psi'
      where
        phi' = translateFormula phi
        psi' = translateFormula psi
        op' =
          case op of
            (TPTP.:<=>:)  -> (.<=>.)
            (TPTP.:=>:)   -> (.=>.)
            (TPTP.:<=:)   -> flip (.=>.)
            (TPTP.:&:)    -> (.&&.)
            (TPTP.:|:)    -> (.||.)
            (TPTP.:~&:)   -> \a b -> notB (a .&&. b)
            (TPTP.:~|:)   -> \a b -> notB (a .||. b)
            (TPTP.:<~>:)  -> \a b -> notB (a .<=>. b)
    eq lhs op rhs =
      case op of
        (TPTP.:=:)  -> MF.Atom $ MF.PApp "=" [lhs', rhs']
        (TPTP.:!=:) -> MF.Not $ MF.Atom $ MF.PApp "=" [lhs', rhs']
      where
        lhs' = translateTerm lhs
        rhs' = translateTerm rhs
    rel (TPTP.AtomicWord p) ts = MF.Atom $ MF.PApp (fromString p) ts'
      where
        ts' = map translateTerm ts

translateTerm :: TPTP.Term -> MF.Term
translateTerm = TPTP.foldT str num var app
  where
    str s = MF.TmApp (fromString (show s)) []
    num r = MF.TmApp (fromString (showRational r)) []
    var (TPTP.V v) = MF.TmVar (fromString v)
    app (TPTP.AtomicWord f) ts = MF.TmApp (fromString f) ts'
      where
        ts' = map translateTerm ts

    showRational r =
      if denominator r == 1
      then show (numerator r)
      else show (numerator r) ++ "/" ++ show (denominator r)

-- ---------------------------------------------------------------------------
