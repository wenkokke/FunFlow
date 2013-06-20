module FUN
  ( module FUN.Base
  , module FUN.Parsing
  , module FUN.Labeling
  , module FUN.W
  , module FUN.CFA
  ) where

import FUN.Base     -- ^ abstract syntax tree
import FUN.Parsing  -- ^ parser
import FUN.Labeling -- ^ labeling
import FUN.W        -- ^ type inference
import FUN.CFA      -- ^ control flow analysis

import Text.Printf (printf)
import qualified Data.Map as M
import Text.ParserCombinators.UU.Utils (runParser)

-- * Top-Level Parsers

parseProg :: String -> Prog
parseProg = runLabel . runParser "stdin" pProg

parseDecl :: String -> Decl
parseDecl = runLabel . runParser "stdin" pDecl

parseExpr :: String -> Expr
parseExpr = runLabel . runParser "stdin" pExpr

-- * Example code

main = either print (putStrLn . put) env
  where
  put :: TyEnv -> String
  put = M.foldWithKey (\k v r -> printf "%s : %s\n%s" k (show v) r) []
  env :: Either TypeError TyEnv
  env = runW examples

examples =
  fmap parseDecl $
  [ "const x y = x"
  , "id x = x"
  , "apply f x = f x"
  , "compose f g x = f (g x)"
  , "fst p = case p of Pair(x,y) in x"
  , "snd p = case p of Pair(x,y) in y"
  , "pair x y = Pair(x,y)"
  , "silly1 p = case p of Pair(f,g) in compose f g"
  , "silly2 p = compose (fst p) (snd p)"
  , "silly3 p x = apply (compose (fst p) (snd p)) (id x)"
  ]