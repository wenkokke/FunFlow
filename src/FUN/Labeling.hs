module FUN.Labeling where

import FUN.Base
import Control.Monad.Supply

class Labelable a where
  label :: a -> Supply Label a
  runLabel :: a -> a
  runLabel a = evalSupply (label a) (fmap (:[]) ['A'..'Z'] ++ fmap show [0..]) 

instance (Labelable a) => (Labelable [a]) where
  label = mapM label
  
instance Labelable Prog where
  label (Prog ds) = do ds <- label ds; return (Prog ds)
  
instance Labelable Decl where
  label (Decl n e) = do e <- label e; return (Decl n e)

instance Labelable Expr where
  label l@(Lit _)         = return l
  label v@(Var _)         = return v
  label (Abs _ n e)       = do l <- supply; e <- label e; return (Abs l n e)
  label (App e1 e2)       = do e1 <- label e1; e2 <- label e2; return (App e1 e2)
  label (Bin n e1 e2)     = do e1 <- label e1; e2 <- label e2; return (Bin n e1 e2)
  label (Let n e1 e2)     = do e1 <- label e1; e2 <- label e2; return (Let n e1 e2)
  label (Fix _ f n e)     = do l <- supply; e <- label e; return (Fix l f n e)
  label (Con _ n e1 e2)   = do l <- supply; e1 <- label e1; e2 <- label e2; return (Con l n e1 e2)
  label (Sum lr _ n e)    = do l <- supply; e <- label e; return (Sum lr l n e)      
  label (Des e1 n a b e2) = do e1 <- label e1; e2 <- label e2; return (Des e1 n a b e2)
  label (ITE b e1 e2)     = do b <- label b; e1 <- label e1; e2 <- label e2; return (ITE b e1 e2)
