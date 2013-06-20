module FUN
  ( module FUN.Base
  , module FUN.Parsing
  , module FUN.W
--  , module FUN.CFA
  ) where

import FUN.Base     -- ^ abstract syntax tree
import FUN.Parsing  -- ^ parser
import FUN.Labeling -- ^ labeling
import FUN.W        -- ^ type inference
--import FUN.CFA      -- ^ control flow analysis

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

--main = either print (putStrLn . put) env
--  where
--  put :: TyEnv -> String
--  put = M.foldWithKey (\k v r -> printf "%s : %s\n%s" k (show v) r) []
--  env :: Either TypeError TyEnv
--  env = runCFA examples

examples =
  fmap parseDecl $
  [ "apply f x = f x"

  , "compose f g x = f (g x)"
  , "id x = x"

  , "lmap f p = case p of Pair (x, y) in Pair (f x, y)"
  , "rmap g p = case p of Pair (x, y) in Pair (x, g y)"
  , "bimap f g = compose (lmap f) (rmap g)"

  , "curry f = fun x y => let p = Pair (x, y) in f p"
  , "uncurry f = fun p => case p of Pair (x, y) in f x y"

  , "pair x y = Pair (x,y)"
  
  , "fst p = case p of Pair(x,y) in x"
  , "snd p = case p of Pair(x,y) in y"

  , "swap p = case p of Pair (x, y) in Pair (y, x)"
  
  , "const x y = x"

  , "ap w = fun f a => case f of Pair (r, g) in case a of Pair (s, x) in Pair (w r s, g x)"
  , "bind w = fun f a => case a of Pair (x, v) in case f v of Pair (y, b) in Pair (w x y, b)" 

  , "silly1 p = case p of Pair(f,g) in compose f g"
  , "silly2 p = compose (fst p) (snd p)"
  , "silly3 p x = apply (compose (fst p) (snd p)) (id x)"

  , "idB = compose curry uncurry" 
  , "idP = fun p => Pair (fst p, snd p)" 
  , "idR = compose uncurry curry"
  ]
