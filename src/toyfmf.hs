-----------------------------------------------------------------------------
-- |
-- Module      :  toyfmf
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- A toy-level model finder
--
-----------------------------------------------------------------------------

import Control.Monad
import Data.IORef
import System.Environment
import System.IO
import qualified Codec.TPTP as TPTP
import qualified FOLModelFinder as MF

main :: IO ()
main = do
  args <- getArgs
  case args of
    [fpath, size] -> solve fpath (read size)
    _ -> hPutStrLn stderr "Usage: toyfmf <file.tptp> <size>"

solve :: FilePath -> Int -> IO ()
solve _ size | size <= 0 = error "<size> should be >=1"
solve fpath size = do
  inputs <- TPTP.parseFile fpath
  let fs = translateProblem inputs

  ref <- newIORef 0
  let skolem name _ = do
        n <- readIORef ref
        let fsym = name ++ "#" ++ show n
        writeIORef ref (n+1)
        return fsym
  cs <- liftM concat $ mapM (MF.toSkolemNF skolem) fs

  ret <- MF.findModel size cs
  case ret of
    Nothing -> do
      putStrLn "s NO MODEL FOUND"
    Just m -> do
      putStrLn "s SATISFIABLE"
      forM_ (MF.showModel m) $ \s ->
        putStrLn $ "v " ++ s

  return ()

-- ---------------------------------------------------------------------------

translateProblem :: [TPTP.TPTP_Input] -> [MF.Formula]
translateProblem inputs = do
  i <- inputs
  case i of
    TPTP.Comment _ -> []
    TPTP.Include _ _ -> error "\"include\" is not supported yet "
    TPTP.AFormula{ TPTP.name = _, TPTP.role = role, TPTP.formula = formula, TPTP.annotations = _ } ->
      return $ translateFormula formula

translateFormula :: TPTP.Formula -> MF.Formula
translateFormula = TPTP.foldF neg quant binop eq rel
  where
    neg phi = MF.Not $ translateFormula phi
    quant q vs phi = foldr q' (translateFormula phi) [v | TPTP.V v <- vs]
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
            (TPTP.:<=>:)  -> MF.Equiv
            (TPTP.:=>:)   -> MF.Imply
            (TPTP.:<=:)   -> flip MF.Imply
            (TPTP.:&:)    -> MF.And
            (TPTP.:|:)    -> MF.Or
            (TPTP.:~&:)   -> \a b -> MF.Not (a `MF.And` b)
            (TPTP.:~|:)   -> \a b -> MF.Not (a `MF.Or` b)
            (TPTP.:<~>:)  -> \a b -> MF.Not (a `MF.Equiv` b)
    eq lhs op rhs =
      case op of
        (TPTP.:=:)  -> MF.Atom $ MF.PApp "=" [lhs', rhs']
        (TPTP.:!=:) -> MF.Not $ MF.Atom $ MF.PApp "=" [lhs', rhs']
      where
        lhs' = translateTerm lhs
        rhs' = translateTerm rhs
    rel (TPTP.AtomicWord p) ts = MF.Atom $ MF.PApp p ts'
      where
        ts' = map translateTerm ts

translateTerm :: TPTP.Term -> MF.Term
translateTerm = TPTP.foldT str num var app
  where
    str s = MF.TmApp (show s) []
    num r = MF.TmApp (show r) []
    var (TPTP.V v) = MF.TmVar v
    app (TPTP.AtomicWord f) ts = MF.TmApp f ts'
      where
        ts' = map translateTerm ts

-- ---------------------------------------------------------------------------
