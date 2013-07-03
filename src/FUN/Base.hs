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
  | Con  Label Name Con
  | Des  Name Expr  Des
  deriving (Eq)
  
data Con
  = Unit
  | Prod Expr Expr
  | Sum  LR Expr
  deriving (Eq)
  
data Des
  = UnUnit Expr
  | UnProd Name Name Expr
  | UnSum  (Name, Expr) (Name, Expr)
  deriving (Eq)

type Name
  = String
  
type Label
  = String
  
noLabel :: Label
noLabel = ""
  
-- * Syntactic sugar for constructing complex structures

unit :: Expr
unit = Con noLabel "()" Unit

-- |Constructs a constructor... whoa.
con :: Name -> Con -> Expr
con = Con noLabel

-- |Constucts a destructor.
-- des :: Name -> Expr -> Des -> Expr
des :: Expr -> Name -> (Name -> Des) -> Expr
des e nm f = Des nm e (f nm)

-- |Constructs a unit destructor.
ununit :: Expr -> (Name -> Des)
ununit e nm = UnUnit e 

-- |Constructs a product destructor.
unprod :: Name -> Name -> Expr -> (Name -> Des)
unprod x y e _ = UnProd x y e

-- |Constructs a sum destructor.
unsum :: Name -> Expr -> Name -> Name -> Expr -> (Name -> Des)
unsum xl el nr xr er nl | nl == nr = UnSum (xl, el) (xr, er)

-- |Construcs a left sum constructor.
suml :: Expr -> Con
suml e = Sum L e

-- |Construcs a left sum constructor.
sumr :: Expr -> Con
sumr e = Sum R e

-- |Constructs a "list" out of a list of expressions.
list :: [Expr] -> Expr
list = foldr cons nil

-- |Constructs a "nil".
nil :: Expr
nil = Con noLabel "List" (Sum L (Con noLabel "Nil" Unit))

-- |Constructs a "cons".
cons :: Expr -> Expr -> Expr
cons x xs = Con noLabel "List" (Sum R (Con noLabel "Cons" (Prod x xs)))

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
        Con l nm  con   -> printf "%s%s%s" nm (showAnn l) (showCon cp nm con)
        Des nm exp des  -> printf "case %s of %s" (showExpr exp) (showDes cp nm des)
  in showExpr

showCon :: Bool -> Name -> Con -> String
showCon cp nm (Unit)     = "()"
showCon cp nm (Prod x y) = printf "%s(%s,%s)" nm (showExpr cp x) (showExpr cp y)
showCon cp nm (Sum L e)  = printf "%s.Left %s" nm (showExpr cp e)
showCon cp nm (Sum R e)  = printf "%s.Right %s" nm (showExpr cp e)

showDes :: Bool -> Name -> Des -> String
showDes cp nm (UnUnit e)           = printf "%s () -> %s" nm (showExpr cp e)
showDes cp nm (UnProd x y e)       = printf "%s(%s,%s) -> %s" nm x y (showExpr cp e)
showDes cp nm (UnSum  (xl, el) (xr, er)) = printf "%s.Left %s -> %s ; %s.Right %s -> %s"
                                             nm xl (showExpr cp el) nm xr (showExpr cp er)

instance Show Prog where show (Prog ds) = unlines (map show ds)
instance Show Decl where show = showDecl False
instance Show Expr where show = showExpr False

--instance Show Con  where show = showCon False
--instance Show Des  where show = showDes False

instance Show Lit where
  show (Bool b)    = show b
  show (Integer i) = show i
