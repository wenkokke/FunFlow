module FUN
  ( module FUN.Base
  , module FUN.Parsing
  , module FUN.CFA
  ) where

import FUN.Base                         -- ^ abstract syntax tree
import FUN.Parsing                      -- ^ parser
import FUN.Labeling                     -- ^ labeling
import FUN.W (runW)                     -- ^ type inference
import FUN.CFA (runCFA,TypeError,TyEnv, Constraint, showType) -- ^ control flow analysis

import Text.Printf (printf)
import qualified Data.Map as M
import qualified Data.Set as S
import Text.ParserCombinators.UU.Utils (runParser)

-- * Top-Level Parsers

parseProg :: String -> Prog
parseProg = runLabel . runParser "stdin" pProg

parseDecl :: String -> Decl
parseDecl = runLabel . runParser "stdin" pDecl

parseExpr :: String -> Expr
parseExpr = runLabel . runParser "stdin" pExpr

-- * Example code

main :: IO ()
main = either print (putStrLn . put) env
  where
  showAnns = True {- True = print annotation variables, False = just print inferred types -}
    
  put :: (TyEnv, S.Set Constraint) -> String
  put (m, w) =  let typePrinter = \k v r -> printf "%s : %s\n%s" k (showType showAnns v) r
                    typeList = M.foldWithKey typePrinter [] m
                    annPrinter = \x xs -> show x ++ "\n" ++ xs
                    annList = "\n" ++ S.fold annPrinter "" w
                in typeList ++ (if showAnns then annList else "")
  env :: Either TypeError (TyEnv, S.Set Constraint)
  env = runCFA ex1
  
ex1 =
  fmap parseDecl $
  [ "apply f x = f x"

  , "compose f g x = f (g x)"
  , "id x = x"

  , "mapFst f p = case p of Pair (x, y) in Pair (f x, y)"
  , "mapSnd g p = case p of Pair (x, y) in Pair (x, g y)"
  , "mapPair f g = compose (mapFst f) (mapSnd g)"

  , "curry f   = fun x y => let p = Pair (x, y) in f p"
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

  , "idPair p = Pair(fst p, snd p)" 
  , "idCurry1 = compose curry uncurry" 
  , "idCurry2 = compose uncurry curry"
  ]
