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
  deriving (Eq)
  
data Expr
  = Lit  Lit
  | Var  Name
  | Fix  Label Name Name Expr
  | Abs  Label Name Expr
  | App  Expr Expr
  | Bin  Name Expr Expr
  | Let  Name Expr Expr
  | ITE  Expr Expr Expr
  | Con  Label Con
  | Des  Expr  Des
  deriving (Eq)
  
data Con
  = Unit Name
  | Prod Name Expr Expr
  | Sum  Name LR Expr
  deriving (Eq)
  
data Des
  = UnUnit Name Expr
  | UnProd Name Name Name Expr
  | UnSum  Name Name Expr Name Expr
  deriving (Eq)

type Name
  = String
  
type Label
  = String
  
noLabel :: Label
noLabel = ""
  
-- * Syntactic sugar for constructing complex structures

-- |Constructs a constructor... whoa.
con :: Con -> Expr
con = Con noLabel

-- |Constucts a destructor.
des :: Expr -> Des -> Expr
des = Des

-- |Constructs a unit destructor.
ununit :: Name -> Expr -> Des
ununit = UnUnit

-- |Constructs a product destructor.
unprod :: Name -> Name -> Name -> Expr -> Des
unprod = UnProd

-- |Construcs a left sum constructor.
suml :: Name -> Expr -> Con
suml n e = Sum n L e

-- |Construcs a left sum constructor.
sumr :: Name -> Expr -> Con
sumr n e = Sum n R e

-- |Constructs a "list" out of a list of expressions.
list :: [Expr] -> Expr
list = foldr cons nil

-- |Constructs a "nil".
nil :: Expr
nil = Con noLabel (Sum "List" L (Con noLabel (Unit "Nil")))

-- |Constructs a "cons".
cons :: Expr -> Expr -> Expr
cons x xs = Con noLabel (Sum "List" R (Con noLabel (Prod "Cons" x xs)))

-- |Constructs a sum destructor.
unsum :: Name -> Name -> Expr -> Name -> Name -> Expr -> Des
unsum nl xl el nr xr er | nl == nr = UnSum nl xl el xr er

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

showDecl :: Bool -> Decl -> String
showDecl cp (Decl n e) = printf "%s = %s" n (showExpr cp e)  

showExpr :: Bool -> Expr -> String
showExpr cp =
  let showAnn  ann = if cp then "[" ++ ann ++ "]" else ""
      showExpr exp = case exp of
        Lit (Bool b)    -> case b of True -> "true"; False -> "false"
        Lit (Integer n) -> show n
        Var n           -> n
        Abs l n e       -> printf "fun %s =%s> %s" n (showAnn l) (showExpr e)
        Fix l f n e     -> printf "fix %s %s =%s> %s" f n (showAnn l) (showExpr e)
        App e1 e2       -> printf "(%s %s)" (showExpr e1) (showExpr e2)
        Bin n e1 e2     -> printf "(%s %s %s)" (showExpr e1) n (showExpr e2)
        Let n e1 e2     -> printf "let %s = %s in %s" n (showExpr e1) (showExpr e2)
        ITE b e1 e2     -> printf "if %s then %s else %s" (showExpr b) (showExpr e1) (showExpr e2)
        Con l   con     -> printf "%s[%s]" (showAnn l) (show con)
        Des exp des     -> printf "case %s of %s" (showExpr exp) (show des)
  in showExpr

showCon :: Bool -> Con -> String
showCon cp (Unit n)     = n
showCon cp (Prod n x y) = printf "%s(%s,%s)" n (showExpr cp x) (showExpr cp y)
showCon cp (Sum n L e)  = printf "%s.Left %s" n (showExpr cp e)
showCon cp (Sum n R e)  = printf "%s.Right %s" n (showExpr cp e)

showDes :: Bool -> Des -> String
showDes cp (UnUnit n e)           = printf "%s -> %s" n (showExpr cp e)
showDes cp (UnProd n x y e)       = printf "%s(%s,%s) -> %s" n x y (showExpr cp e)
showDes cp (UnSum  n xl el xr er) = printf "%s.Left %s -> %s ; %s.Right %s -> %s"
                                      n xl (showExpr cp el) n xr (showExpr cp er)

instance Show Prog where show (Prog ds) = unlines (map show ds)
instance Show Decl where show = showDecl False
instance Show Expr where show = showExpr False
instance Show Con  where show = showCon False
instance Show Des  where show = showDes False

instance Show Lit where
  show (Bool b)    = show b
  show (Integer i) = show i
