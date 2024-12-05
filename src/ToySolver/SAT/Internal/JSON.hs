{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module ToySolver.SAT.Internal.JSON where

import Control.Applicative
import Control.Arrow ((***))
import Control.Monad
import qualified Data.Aeson as J
import qualified Data.Aeson.Types as J
import Data.Aeson ((.=), (.:))
import Data.String
import qualified Data.Text as T

import qualified Data.PseudoBoolean as PBFile
import ToySolver.Internal.JSON
import qualified ToySolver.SAT.Types as SAT

jVar :: SAT.Var -> J.Value
jVar v = J.object
  [ "type" .= ("variable" :: J.Value)
  , "name" .= (jVarName v :: J.Value)
  ]

jVarName :: IsString a => SAT.Var -> a
jVarName v = fromString ("x" ++ show v)

jLitName :: IsString a => SAT.Var -> a
jLitName v
  | v >= 0 = jVarName v
  | otherwise = fromString ("~x" ++ show (- v))

parseVar :: J.Value -> J.Parser SAT.Var
parseVar = withTypedObject "variable" $ \obj -> parseVarName =<< obj .: "name"

parseVarName :: J.Value -> J.Parser SAT.Var
parseVarName = J.withText "variable name" parseVarNameText

parseVarNameText :: T.Text -> J.Parser SAT.Var
parseVarNameText name =
  case T.uncons name of
    Just ('x', rest) | (x,[]) : _ <- reads (T.unpack rest) -> pure x
    _ -> fail ("failed to parse variable name: " ++ show name)

jNot :: J.Value -> J.Value
jNot x = J.object
  [ "type" .= ("operator" :: J.Value)
  , "name" .= ("not" :: J.Value)
  , "operands" .= [x]
  ]

jLit :: SAT.Lit -> J.Value
jLit l
  | l > 0 = jVar l
  | otherwise = jNot $ jVar (- l)

parseLit :: J.Value -> J.Parser SAT.Lit
parseLit x = parseVar x <|> withNot (fmap negate . parseVar) x

parseLitName :: J.Value -> J.Parser SAT.Lit
parseLitName = J.withText "literal" parseLitNameText

parseLitNameText :: T.Text -> J.Parser SAT.Lit
parseLitNameText name =
  case T.uncons name of
    Just ('~', rest) -> negate <$> parseVarNameText rest
    _ -> parseVarNameText name

jConst :: J.ToJSON a => a -> J.Value
jConst x = J.object ["type" .= ("constant" :: J.Value), "value" .= x]

parseConst :: J.FromJSON a => J.Value -> J.Parser a
parseConst = withTypedObject "constant" $ \obj -> obj .: "value"

jPBSum :: SAT.PBSum -> J.Value
jPBSum s = J.object
  [ "type" .= ("operator" :: J.Value)
  , "name" .= ("+" :: J.Value)
  , "operands" .=
      [ J.object
          [ "type" .= ("operator" :: J.Value)
          , "name" .= ("*" :: J.Value)
          , "operands" .= (jConst c : [jLit lit | lit <- lits])
          ]
      | (c, lits) <- s
      ]
  ]

parsePBSum :: J.Value -> J.Parser SAT.PBSum
parsePBSum x = msum
  [ withOperator "+" (fmap concat . mapM parsePBSum) x
  , f x >>= \term -> pure [term]
  ]
  where
    f :: J.Value -> J.Parser (Integer, [SAT.Lit])
    f y = msum
      [ parseConst y >>= \c -> pure (c, [])
      , parseLit y >>= \lit -> pure (1, [lit])
      , withOperator "*" (fmap ((product *** concat) . unzip) . mapM f) y
      ]

jPBConstraint :: PBFile.Constraint -> J.Value
jPBConstraint (lhs, op, rhs) =
  J.object
  [ "type" .= ("operator" :: J.Value)
  , "name" .= (case op of{ PBFile.Ge -> ">="; PBFile.Eq -> "=" } :: J.Value)
  , "operands" .= [jPBSum lhs, jConst rhs]
  ]

parsePBConstraint :: J.Value -> J.Parser PBFile.Constraint
parsePBConstraint x = msum
  [ withOperator ">=" (f PBFile.Ge ">=") x
  , withOperator "=" (f PBFile.Eq "=") x
  ]
  where
    f :: PBFile.Op -> String -> [J.Value] -> J.Parser PBFile.Constraint
    f op _opStr [lhs, rhs] = do
      lhs' <- parsePBSum lhs
      rhs' <- parseConst rhs
      pure (lhs', op, rhs')
    f _ opStr operands = fail ("wrong number of arguments for " ++ show opStr ++ " (given " ++ show (length operands) ++ ", expected 1)")


withOperator :: String -> ([J.Value] -> J.Parser a) -> J.Value -> J.Parser a
withOperator name k = withTypedObject "operator" $ \obj -> do
  op <- obj .: "name"
  unless (name == op) $ fail ("expected operator name " ++ show name ++ ", but found type " ++ show op)
  operands <- obj .: "operands"
  k operands

withNot :: (J.Value -> J.Parser a) -> J.Value -> J.Parser a
withNot k = withOperator "not" $ \operands -> do
  case operands of
    [x] -> k x
    _ -> fail ("wrong number of arguments for \"not\" (given " ++ show (length operands) ++ ", expected 1)")

withAnd :: ([J.Value] -> J.Parser a) -> J.Value -> J.Parser a
withAnd = withOperator "and"

withOr :: ([J.Value] -> J.Parser a) -> J.Value -> J.Parser a
withOr = withOperator "or"

withITE :: (J.Value -> J.Value -> J.Value -> J.Parser a) -> J.Value -> J.Parser a
withITE k = withOperator "ite" $ \operands -> do
  case operands of
    [c, t, e] -> k c t e
    _ -> fail ("wrong number of arguments for \"ite\" (given " ++ show (length operands) ++ ", expected 3)")

withImply :: (J.Value -> J.Value -> J.Parser a) -> J.Value -> J.Parser a
withImply k = withOperator "=>" $ \operands -> do
  case operands of
    [a, b] -> k a b
    _ -> fail ("wrong number of arguments for \"=>\" (given " ++ show (length operands) ++ ", expected 2)")

withEquiv :: (J.Value -> J.Value -> J.Parser a) -> J.Value -> J.Parser a
withEquiv k = withOperator "<=>" $ \operands -> do
  case operands of
    [a, b] -> k a b
    _ -> fail ("wrong number of arguments for \"<=>\" (given " ++ show (length operands) ++ ", expected 2)")
