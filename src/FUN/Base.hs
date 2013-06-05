module FUN.Base where

import Prelude hiding (abs)

-- * Abstract syntax tree for the FUN language

type Name
  = String

data Lit
  = Bool Bool
  | Integer Integer
  deriving (Eq,Show)
  
data Expr
  = Lit Lit
  | Var Name
  | Abs Name Expr
  | App Expr Expr
  | Bin Name Expr Expr
  | Let Name Expr Expr
  | Fix Name Name Expr
  | Con Name [Expr]
  | Des Expr Name [Name] Expr
  | ITE Expr Expr Expr
  deriving (Eq,Show)

-- * Syntactic sugar for constructing complex structures
  
-- |Constructs an N-ary lambda abstraction
abs :: [Name] -> Expr -> Expr
abs xs e = foldr Abs e xs

-- |Constructs an N-ary recursive lambda abstraction
fix :: [Name] -> Expr -> Expr
fix (f:x:xs) e = Fix f x (abs xs e)

-- |Constructs let bindings with multiple definitions
letn :: [(Name,Expr)] -> Expr -> Expr
letn defs e = foldr (uncurry Let) e defs
  
-- |Constructs a binary operator
bin :: Name -> Expr -> Expr -> Expr
bin op x y = App (App (Var op) x) y
