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
  
data Expr
  = Lit Lit
  | Var Name
  | Abs Label Name Expr
  | App Expr Expr
  | Bin Name Expr Expr
  | Let Name Expr Expr
  | Fix Label Name Name Expr
  | Con Label Name Expr Expr      -- ^ con constructor arg0 arg1
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
  
instance Show Decl where
  show (Decl n e) = printf "%s = %s" n (show e)
  
instance Show Expr where
  show (Lit l) = show l
  show (Var n) = n
  show (Abs l n e) = printf "fun %s =%s> %s" n l (show e)
  show (App e1 e2) = printf "(%s %s)" (show e1) (show e2)
  show (Bin n e1 e2) = printf "(%s %s %s)" (show e1) n (show e2)
  show (Let n e1 e2) = printf "let %s = %s in %s" n (show e1) (show e2)
  show (Fix l f n e) = printf "fix %s %s =%s> %s" f n l (show e)
  show (Con l n e1 e2) = printf "%s[%s](%s,%s)" n (show l) (show e1) (show e1)
  show (Des e1 n a b e2) = printf "case %s of %s(%s,%s) in %s" (show e1) n a b (show e1)
  show (ITE b e1 e2) = printf "if %s then %s else %s" (show b) (show e1) (show e2)
  
instance Show Lit where
  show (Bool b) = show b
  show (Integer i) = show i
