module FUN
  ( module FUN.Base
  , module FUN.Parsing
  , module FUN.CFA
  ) where

import FUN.Base                         -- ^ abstract syntax tree
import FUN.Parsing                      -- ^ parser
import FUN.Labeling                     -- ^ labeling
import FUN.W (runW)                     -- ^ type inference
import FUN.CFA 
  ( runCFA, TypeError, Env, Constraint, showType
  , printFlow, solveConstraints, TVar (..), Type (..)
  ) -- ^ control flow analysis

import Text.Printf (printf)
import qualified Data.Map as M
import qualified Data.Set as S
import Text.ParserCombinators.UU.Utils (runParser)

-- * Top-Level Parsers

parseProg :: String -> Prog
parseProg = runParser "stdin" pProg

parseDecl :: String -> Decl
parseDecl = runParser "stdin" pDecl

parseExpr :: String -> Expr
parseExpr = runParser "stdin" pExpr

-- * Example code

printProgram :: [Decl] -> Env -> String
printProgram p env = 
  let funcType (Decl nm e) = case M.lookup nm (fst env) of
                               Just r  -> nm ++ " :: " ++ (showType annotations r)
                               Nothing -> error $ "printProgram: no matching type found for function \"" ++ nm ++ "\""
      funcBody = showDecl annotations
      prefix = "{\n"
      suffix = "}"
      
      printer x xs = "  " ++ funcType x ++ "\n  " ++ funcBody x ++ "\n\n" ++ xs 
      
  in prefix ++ foldr printer "" p ++ suffix
  
annotations :: Bool
annotations = False
  
main :: IO ()
main = 
  let prog = example
        
      put :: (Env, S.Set Constraint) -> String
      put (m, w) =  let programInfo = "program = " ++ printProgram prog m
                        annInfo  = "control flow = " ++ (printFlow . solveConstraints $ w)
                        
                    in    programInfo ++ "\n\n"
                       ++ annInfo     ++ "\n\n"
                       
      env :: Either TypeError (Env, S.Set Constraint)
      env = runCFA prog
  in either print (putStrLn . put) env
        
exCategory = fmap parseDecl $
  [ "compose f g x = f (g x)"
  , "id x = x"
  ]

exPair = fmap parseDecl $
  [ "pair x y = Pair (x,y)"
  , "fst p = case p of Pair(x,y) -> x"
  , "snd p = case p of Pair(x,y) -> y"
  , "swap p = case p of Pair (x, y) -> Pair (y, x)"
  ]

exCurry = fmap parseDecl $
  [ "curry f   = fun x y => let p = Pair (x, y) in f p"
  , "uncurry f = fun p => case p of Pair (x, y) -> f x y"
  ]
  
exMap = fmap parseDecl $
  [ "mapFst f p = case p of Pair (x, y) -> Pair (f x, y)"
  , "mapSnd g p = case p of Pair (x, y) -> Pair (x, g y)"
  , "mapPair f g = compose (mapFst f) (mapSnd g)"
  ]
  
exId = fmap parseDecl $
  [ "idPair p = Pair(fst p, snd p)" 
  , "idCurry1 = compose curry uncurry" 
  , "idCurry2 = compose uncurry curry"
  ]
  
exFunction = fmap parseDecl $
  [ "apply f x = f x"
  
  , "const x y = x"

  , "ap w = fun f a => case f of Pair (r, g) -> case a of Pair (s, x) -> Pair (w r s, g x)"
  , "bind w = fun f a => case a of Pair (x, v) -> case f v of Pair (y, b) -> Pair (w x y, b)" 
  ]

exSilly = fmap parseDecl $
  [ "silly1 p = case p of Pair(f,g) -> compose f g"
  , "silly2 p = compose (fst p) (snd p)"
  , "silly3 p x = apply (compose (fst p) (snd p)) (id x)"
  ]

  
exLoop = fmap parseDecl $
  if True then
  [ "fy = fun y => y"
  , "g = fix f x => f fy"
  , "fz = fun z => z"
  , "test = g fz"
  ] else
  [ "loop = let g = fix f x => f (fun y => y) in g (fun z => z)"
  ]
  
exPairimental = fmap parseDecl $
  [ "pA = Pair (3, 5)"
  , "pB = Pair (7, 11)"
  , "f p = case p of Pair (x, y) -> x" 
  ]
  
exSum = fmap parseDecl $
  [ "sumL = Either.Left 5"
  , "sumR = Either.Right false"
  , "sumLR = if false then sumL else sumR"
  , "sumLL = if false then sumL else sumL"
  , "sumRR = if false then sumR else sumR"
  , "killSumLR p = case p of Either.Left x -> x"
 ++ "                        Either.Right y -> y"
  , "killSumL p = case p of Either.Left x -> false"
 ++ "                       Either.Right y -> y"
  , "killSumR p = case p of Either.Left x -> x"
 ++ "                       Either.Right y -> false"
  ]

exNats = fmap parseDecl $
  [ "add a = fix add b => case b of"
 ++ "                       Nat.Left u -> case u of () -> a"
 ++ "                       Nat.Right g -> Nat.Right (add g)"
  ]

exUnion = concat $
  [ exCategory
  , exPair
  , exCurry 
  , exMap
  , exId
  , exFunction
  , exLoop
  , exSilly
  , exPairimental
  , exSum
  ]
  
example = runLabel $ exUnion  
