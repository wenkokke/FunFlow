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
  ( runCFA, TypeError,TyEnv, Constraint, showType
  , printFlow, organiseFlow
  ) -- ^ control flow analysis

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

printProgram :: [Decl] -> String
printProgram p = "{\n" ++ foldr (\x xs -> "  " ++ show x ++ "\n" ++ xs) "\n"  p ++ "}"

main :: IO ()
main = 
  let showAnns = True {- True = print annotation variables, False = just print inferred types -}
        
      program = ex1
        
      put :: (TyEnv, S.Set Constraint) -> String
      put (m, w) =  let typePrinter = \k v r -> "  " ++ k ++ " :: " ++ (showType showAnns v) ++ "\n" ++ r
                        typeList = "{\n" ++ M.foldWithKey typePrinter [] m ++ "}"
                        
                        programInfo = "program = " ++ printProgram program
                        annInfo  = "control flow = " ++ (printFlow . organiseFlow $ w)
                        typeInfo = "inferred toplevel types = " ++ typeList 
                        
                        
                    in    programInfo ++ "\n\n"
                       ++ annInfo     ++ "\n\n"
                       ++ typeInfo    ++ "\n\n"
      env :: Either TypeError (TyEnv, S.Set Constraint)
      env = runCFA program
  in either print (putStrLn . put) env
        

exMap = runLabel . fmap parseDecl $
  [ "mapFst f p = case p of Pair (x, y) in Pair (f x, y)"
  , "mapSnd g p = case p of Pair (x, y) in Pair (x, g y)"
  , "mapPair f g = compose (mapFst f) (mapSnd g)"
  ]
  
exPair = runLabel . fmap parseDecl $
  [ "pair x y = Pair (x,y)"
  , "fst p = case p of Pair(x,y) in x"
  , "snd p = case p of Pair(x,y) in y"
  , "swap p = case p of Pair (x, y) in Pair (y, x)"
  ]
 
expCurry = runLabel . fmap parseDecl $
  [ "curry f   = fun x y => let p = Pair (x, y) in f p"
  , "uncurry f = fun p => case p of Pair (x, y) in f x y"
  ]
 
exCategory = runLabel . fmap parseDecl $
  [ "compose f g x = f (g x)"
  , "id x = x"
  ]

exSilly = runLabel . fmap parseDecl $
  [ "silly1 p = case p of Pair(f,g) in compose f g"
  , "silly2 p = compose (fst p) (snd p)"
  , "silly3 p x = apply (compose (fst p) (snd p)) (id x)"
  ]

exId = runLabel . fmap parseDecl $
  [ "idPair p = Pair(fst p, snd p)" 
  , "idCurry1 = compose curry uncurry" 
  , "idCurry2 = compose uncurry curry"
  ]
  
exFunction =
  runLabel . fmap parseDecl $
  [ "apply f x = f x"
  
  , "const x y = x"

  , "ap w = fun f a => case f of Pair (r, g) in case a of Pair (s, x) in Pair (w r s, g x)"
  , "bind w = fun f a => case a of Pair (x, v) in case f v of Pair (y, b) in Pair (w x y, b)" 
  ]

exLoop = runLabel . fmap parseDecl $
  if False then
  [ "fy = fun y => y"
  , "g = fix f x => f fy"
  , "fz = fun z => z"
  , "test = g fz"
  ] else
  [ "loop = let g = fix f x => f (fun y => y) in g (fun z => z)"
  ]
  
ex1 = exLoop
  