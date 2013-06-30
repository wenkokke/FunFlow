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
  ( runCFA, TypeError, TyEnv, Constraint, showType
  , printFlow, organiseFlow, TVar (..), Type (..)
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

printProgram :: [Decl] -> M.Map TVar Type -> String
printProgram p env = 
  let showAnns = True
      
      funcType (Decl nm e) = case M.lookup nm env of
                               Just r  -> nm ++ " :: " ++ (showType showAnns r)
                               Nothing -> error $ "printProgram: no matching type found for function \"" ++ nm ++ "\""
      funcBody = show
      prefix = "{\n"
      suffix = "}"
      
      printer x xs = "  " ++ funcType x ++ "\n  " ++ funcBody x ++ "\n\n" ++ xs 
      
  in prefix ++ foldr printer "" p ++ suffix

main :: IO ()
main = 
  let program = ex1
        
      put :: (TyEnv, S.Set Constraint) -> String
      put (m, w) =  let programInfo = "program = " ++ printProgram program m
                        annInfo  = "control flow = " ++ (printFlow . organiseFlow $ w)
                        
                    in    programInfo ++ "\n\n"
                       ++ annInfo     ++ "\n\n"
                       
      env :: Either TypeError (TyEnv, S.Set Constraint)
      env = runCFA program
  in either print (putStrLn . put) env
        
exCategory = fmap parseDecl $
  [ "compose f g x = f (g x)"
  , "id x = x"
  ]

exPair = fmap parseDecl $
  [ "pair x y = Pair (x,y)"
  , "fst p = case p of Pair(x,y) in x"
  , "snd p = case p of Pair(x,y) in y"
  , "swap p = case p of Pair (x, y) in Pair (y, x)"
  ]

exCurry = fmap parseDecl $
  [ "curry f   = fun x y => let p = Pair (x, y) in f p"
  , "uncurry f = fun p => case p of Pair (x, y) in f x y"
  ]
  
exMap = fmap parseDecl $
  [ "mapFst f p = case p of Pair (x, y) in Pair (f x, y)"
  , "mapSnd g p = case p of Pair (x, y) in Pair (x, g y)"
  , "mapPair f g = compose (mapFst f) (mapSnd g)"
  ]
  
exId = fmap parseDecl $
  [ "idPair p = Pair(fst p, snd p)" 
  , "idCurry1 = compose curry uncurry" 
  , "idCurry2 = compose uncurry curry"
  ]
  
exFunction =
  fmap parseDecl $
  [ "apply f x = f x"
  
  , "const x y = x"

  , "ap w = fun f a => case f of Pair (r, g) in case a of Pair (s, x) in Pair (w r s, g x)"
  , "bind w = fun f a => case a of Pair (x, v) in case f v of Pair (y, b) in Pair (w x y, b)" 
  ]

exSilly = fmap parseDecl $
  [ "silly1 p = case p of Pair(f,g) in compose f g"
  , "silly2 p = compose (fst p) (snd p)"
  , "silly3 p x = apply (compose (fst p) (snd p)) (id x)"
  ]

  
exLoop = fmap parseDecl $
  if False then
  [ "fy = fun y => y"
  , "g = fix f x => f fy"
  , "fz = fun z => z"
  , "test = g fz"
  ] else
  [ "loop = let g = fix f x => f (fun y => y) in g (fun z => z)"
  ]
  
exUnion = runLabel . concat $
  [ exCategory
  , exPair
  , exCurry 
  , exMap
  , exId
  , exFunction
  , exLoop
  , exSilly
  ]
  
ex1 = exUnion
  