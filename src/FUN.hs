module FUN
  ( module FUN.Base
  , module FUN.Parsing
  , module FUN.W
  ) where

import FUN.Base     -- ^ abstract syntax tree
import FUN.Parsing  -- ^ parser
import FUN.W        -- ^ type inference

import Data.Monoid (mempty)
import Control.Monad.Supply
import Control.Monad.Error
import Text.ParserCombinators.UU.Utils (runParser)

parse :: String -> Expr
parse = runParser "stdin" pExpr

runW :: Expr -> Either WError Type
runW e = fmap fst (evalSupply (runErrorT (w (mempty,e))) freshNames)

main :: IO ()
main = either print print (runW (parse "fun x y => x"))
