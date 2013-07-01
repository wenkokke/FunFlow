module FUN.Base where

import Prelude hiding (abs)
import Text.Printf (printf)

-- * Abstract syntax tree for the FUN language

data Prog
  = Prog [Decl]
  deriving (Eq)

data Decl
  = Decl Name Expr
  deriving (Eq)

data Lit
  = Bool Bool
  | Integer Integer
  deriving (Eq)
  
data LR = L | R
  deriving Eq
  
data Expr
  = Lit Lit
  | Var Name
  | Fix Label Name Name Expr
  | Abs Label Name Expr
  | App Expr Expr
  | Bin Name Expr Expr
  | Let Name Expr Expr
  | Con    Label Name Expr Expr   -- ^ con constructor arg0 arg1
  | Sum LR Label Name Expr
  | Des Expr Name Name Name Expr  -- ^ as constructor arg0 arg1 destruct e1 in e2
  | ITE Expr Expr Expr
  deriving (Eq)

type Name
  = String
  
type Label
  = String
  
noLabel :: Label
noLabel = ""
  
-- * Syntactic sugar for constructing complex structures

-- |Constructs an N-ary cartesian product construction
con :: Name -> [Expr] -> Expr
con n xs = foldr1 (Con noLabel n) xs

sum :: LR -> Name -> Expr -> Expr
sum lr nm = Sum lr noLabel nm  

-- |Constructs an N-ary cartesian product destruction
des :: Expr -> Name -> [Name] -> Expr -> Expr
des e1 n (x:y:xs) e2 = Des e1 n x y e2

-- |Constructs an N-ary lambda abstraction
abs :: [Name] -> Expr -> Expr
abs xs e = foldr (Abs noLabel) e xs

-- |Constructs an N-ary recursive lambda abstraction
fix :: [Name] -> Expr -> Expr
fix (f:x:xs) e = Fix noLabel f x (abs xs e)

-- |Constructs a definition tuple.
decl n xs e = Decl n (foldr (Abs noLabel) e xs)

-- |Constructs let bindings with multiple definitions
letn :: [Decl] -> Expr -> Expr
letn defs e = foldr (\(Decl x e) -> Let x e) e defs
  
-- |Constructs a binary operator
bin :: Name -> Expr -> Expr -> Expr
bin op x y = App (App (Var op) x) y

-- * Printing AST as program

instance Show Prog where
  show (Prog ds) = concat (map ((++"\n") . show) ds)

showDecl :: Bool -> Decl -> String
showDecl cp (Decl n e) = printf "%s = %s" n (showExpr cp e)  
      
instance Show Decl where
  show = showDecl False
    
showExpr :: Bool -> Expr -> String
showExpr cp =
  let showAnn a = if cp then "[" ++ a ++ "]" else ""
      showExpr exp = case exp of
        Lit l            -> show l
        Var n            -> n
        Abs l n e        -> printf "fun %s =%s> %s" n (showAnn l) (showExpr e)
        Fix l f n e      -> printf "fix %s %s =%s> %s" f n (showAnn l) (showExpr e)
        App e1 e2        -> printf "(%s %s)" (showExpr e1) (showExpr e2)
        Bin n e1 e2      -> printf "(%s %s %s)" (showExpr e1) n (showExpr e2)
        Let n e1 e2      -> printf "let %s = %s in %s" n (showExpr e1) (showExpr e2)
        Con pi nm e1 e2  -> printf "%s%s (%s,%s)" nm (showAnn pi) (showExpr e1) (showExpr e2)
        Sum lr pi nm e   -> let printSide = case lr of L -> "L%"; R -> "R%"
                            in printSide ++ nm ++ (showAnn pi) ++ " (" ++ showExpr e ++ ")"
        Des e1 n a b e2  -> printf "case %s of %s(%s,%s) in %s" (showExpr e1) n a b (showExpr e2)
        ITE b e1 e2      -> printf "if %s then %s else %s" (showExpr b) (showExpr e1) (showExpr e2)
  in showExpr
  
instance Show Expr where
  show = showExpr False

  
instance Show Lit where
  show (Bool b) = show b
  show (Integer i) = show i
