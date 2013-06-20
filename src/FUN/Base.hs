module FUN.Base where

import Prelude hiding (abs)

-- * Abstract syntax tree for the FUN language

data Prog
  = Prog [Decl]

data Decl
  = Decl Name Expr

data Lit
  = Bool Bool
  | Integer Integer
  deriving (Eq,Show)
  
data Expr
  = Lit Lit
  | Var Name
  | Abs Label Name Expr
  | App Expr Expr
  | Bin Name Expr Expr
  | Let Name Expr Expr
  | Fix Name Name Expr
  | Con Name Expr Expr            -- ^ con constructor arg0 arg1
  | Des Expr Name Name Name Expr  -- ^ as constructor arg0 arg1 destruct e1 in e2
  | ITE Expr Expr Expr
  deriving (Eq,Show)

type Name
  = String
  
type Label
  = Integer
  
noLabel :: Label
noLabel = undefined
  
-- * Syntactic sugar for constructing complex structures

-- |Constructs an N-ary cartesian product construction
con :: Name -> [Expr] -> Expr
con n xs = foldr1 (Con n) xs

-- |Constructs an N-ary cartesian product destruction
des :: Expr -> Name -> [Name] -> Expr -> Expr
des e1 n (x:y:xs) e2 = Des e1 n x y e2

-- |Constructs an N-ary lambda abstraction
abs :: [Name] -> Expr -> Expr
abs xs e = foldr (Abs noLabel) e xs

-- |Constructs an N-ary recursive lambda abstraction
fix :: [Name] -> Expr -> Expr
fix (f:x:xs) e = Fix f x (abs xs e)

-- |Constructs a definition tuple.
decl n xs e = Decl n (foldr (Abs noLabel) e xs)

-- |Constructs let bindings with multiple definitions
letn :: [Decl] -> Expr -> Expr
letn defs e = foldr (\(Decl x e) -> Let x e) e defs
  
-- |Constructs a binary operator
bin :: Name -> Expr -> Expr -> Expr
bin op x y = App (App (Var op) x) y
