module FUN.W where

import Prelude hiding (mapM)
import FUN.Base
import Text.Printf (printf)
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.List as L (union)
import Data.Monoid hiding ((<>))
import Data.Traversable (forM,mapM)
import Debug.Trace (trace)
import Control.Monad (join)
import Control.Monad.Error (Error (..),ErrorT,runErrorT,throwError)
import Control.Monad.Supply (Supply,supply,evalSupply)
import Control.Monad.Trans (lift)

-- * Type definitions

data Type
  = TyCon  Name
  | TyVar  Name
  | TyArr  Type Type
  | TySum  Name Type Type
  | TyProd Name Type Type
  deriving (Eq)
  
instance Show Type where
  show (TyCon  n    ) = n
  show (TyVar  n    ) = n
  show (TyArr    a b) = printf "%s -> %s" (wrap a) (wrap b)
    where
    wrap ty@(TyArr _ _) = printf "(%s)" (show ty)
    wrap ty             = show ty
  show (TySum n a b) = printf "%s %s %s" n (wrap a) (wrap b)
    where
    wrap ty@(TyProd _ _ _) = printf "(%s)" (show ty)
    wrap ty@(TySum  _ _ _) = printf "(%s)" (show ty)
    wrap ty@(TyArr  _ _)   = printf "(%s)" (show ty)
    wrap ty                = show ty
  show (TyProd n a b) = printf "%s %s %s" n (wrap a) (wrap b)
    where
    wrap ty@(TyProd _ _ _) = printf "(%s)" (show ty)
    wrap ty@(TySum  _ _ _) = printf "(%s)" (show ty)
    wrap ty@(TyArr  _ _)   = printf "(%s)" (show ty)
    wrap ty                = show ty
    
-- * Algorithm W for Type Inference

-- |Runs algorithm W on a list of declarations, making each previous
--  declaration an available expression in the next.
runW :: [Decl] -> Either TypeError TyEnv
runW = refreshAll . withFreshNames . foldl addDecl (return mempty)
  where
  addDecl :: W TyEnv -> Decl-> W TyEnv
  addDecl env (Decl x e) = do env <- env;
                              (t,_) <- w e env;
                              return (M.insert x t env)

-- |Provides an infinite stream of names to things in the @W@ monad,
--  reducing it to just an @Either@ value containing perhaps a TypeError.
withFreshNames :: W a -> Either TypeError a
withFreshNames x = evalSupply (runErrorT x) freshNames
  where
  freshNames = letters ++ numbers
    where
    letters = fmap (: []) ['a'..'z']
    numbers = fmap (('t' :) . show) [0..]
    
-- |Refreshes all entries in a type environment.
refreshAll :: Either TypeError TyEnv -> Either TypeError TyEnv
refreshAll env = do env <- env; mapM (withFreshNames . refresh) env

-- |Replaces every type variable with a fresh one.
refresh :: Type -> W Type
refresh t1 = do subs <- forM (ftv t1)
                        $ \a ->
                          do b <- fresh;
                             return (M.singleton a b)
                return (subst (mconcat subs) t1)

-- |Returns the set of free type variables in a type.
ftv :: Type -> [Name]
ftv (TyCon      _) = [ ]
ftv (TyVar      n) = [n]
ftv (TyArr    a b) = L.union (ftv a) (ftv b)
ftv (TySum  _ a b) = L.union (ftv a) (ftv b)
ftv (TyProd _ a b) = L.union (ftv a) (ftv b)
  
type TySubst = Map Name Type

-- |Substitutes a type for a type variable in a type.
subst :: TySubst -> Type -> Type
subst m c@(TyCon _)    = c
subst m v@(TyVar n)    = M.findWithDefault v n m
subst m (TyArr    a b) = TyArr    (subst m a) (subst m b)
subst m (TySum  n a b) = TySum  n (subst m a) (subst m b)
subst m (TyProd n a b) = TyProd n (subst m a) (subst m b)

type TyEnv = Map Name Type

-- |Representation for possible errors in algorithm W.
data TypeError
  = CannotDestruct  Type      -- ^ thrown when attempting to destruct a non-product
  | PatternError    Name Name -- ^ thrown when pattern matching on a different type
  | UnboundVariable Name      -- ^ thrown when unknown variable is encountered
  | OccursCheck     Name Type -- ^ thrown when occurs check in unify fails
  | CannotUnify     Type Type -- ^ thrown when types cannot be unified
  | OtherError      String    -- ^ stores miscellaneous errors
  | NoMsg                     -- ^ please don't be a jackass; don't use this
  deriving Eq

instance Error TypeError where
  noMsg       = NoMsg
  strMsg msg  = OtherError msg

instance Show TypeError where
  show (CannotDestruct   t) = printf "Cannot deconstruct expression of type %s" (show t)
  show (PatternError   a b) = printf "Cannot match pattern %s with %s" a b
  show (UnboundVariable  n) = printf "Unknown variable %s" n
  show (OccursCheck    n t) = printf "Occurs check fails: %s occurs in %s" n (show t)
  show (CannotUnify    a b) = printf "Cannot unify %s with %s" (show a) (show b)
  show (OtherError     msg) = msg
  show (NoMsg             ) = "nope"

type W a = ErrorT TypeError (Supply Name) a

-- |Occurs check for Robinson's unification algorithm.
occurs :: Name -> Type -> Bool
occurs n t = n `elem` (ftv t)

-- |Unification as per Robinson's unification algorithm.
u :: Type -> Type -> W TySubst
u t1@(TyCon a) t2@(TyCon b)
  | a == b        = return mempty
  | otherwise     = throwError (CannotUnify t1 t2)
u (TyArr a1 b1) (TyArr a2 b2)
                  = do s1 <- u a1 a2;
                       s2 <- u (subst s1 b1) (subst s1 b2);
                       return (s2 <> s1)
u t1@(TyProd n1 x1 y1) t2@(TyProd n2 x2 y2)
                  = if n1 == n2
                    then do s1 <- u x1 x2;
                            s2 <- u (subst s1 y1) (subst s1 y2);
                            return (s2 <> s1)
                    else do throwError (CannotUnify t1 t2)
u t1@(TySum n1 x1 y1) t2@(TySum n2 x2 y2)
                  = if n1 == n2
                    then do s1 <- u x1 x2;
                            s2 <- u (subst s1 y1) (subst s1 y2);
                            return (s2 <> s1)
                    else do throwError (CannotUnify t1 t2)
u t1 (TyVar n)
  | n `occurs` t1 = throwError (OccursCheck n t1)
  | otherwise     = return (M.singleton n t1)
u (TyVar n) t2
  | n `occurs` t2 = throwError (OccursCheck n t2)
  | otherwise     = return (M.singleton n t2)
u t1 t2           = throwError (CannotUnify t1 t2)

typeOf :: Lit -> Type
typeOf (Bool    _) = TyCon "Bool"
typeOf (Integer _ _ _) = TyCon "Integer"

fresh :: W Type
fresh = do x <- lift supply; return (TyVar x)

(~>) :: Name -> Type -> TyEnv -> TyEnv
(~>) = M.insert

(<>) :: TySubst -> TySubst -> TySubst
(<>) s2 s1 = M.union s2 (fmap (subst s2) s1)
           
-- |Algorithm W for type inference.
w :: Expr -> TyEnv -> W (Type,TySubst)
w exp env = case exp of
  Lit l           -> return (typeOf l,mempty)
  
  Var n           -> case M.lookup n env of
                        Just  v -> return (v,mempty)
                        Nothing -> throwError (UnboundVariable n)
  
  Abs _ x e       -> do a <- fresh;
                        (t1,s1) <- w e . (x ~> a) $ env;
                        return (TyArr (subst s1 a) t1,s1)
  
  App f e         -> do (t1,s1) <- w f $ env;
                        (t2,s2) <- w e . fmap (subst s1) $ env;
                        a  <- fresh;
                        s3 <- u (subst s2 t1) (TyArr t2 a);
                        return (subst s3 a, s3<>s2<>s1)
  
  Let x e1 e2     -> do (t1,s1) <- w e1 $ env;
                        (t2,s2) <- w e2 . (x ~> t1) . fmap (subst s1) $ env;
                        return (t2, s2<>s1)

  -- * adding fixpoint operators
  
  Fix _ f x e     -> do a <- fresh;
                        b <- fresh;
                        let g = TyArr a b;
                        (t1,s1) <- w e . (f ~> g) . (x ~> a) $ env;
                        s2 <- u t1 (subst s1 b);
                        return (TyArr (subst (s2<>s1) a) (subst s2 t1), s2<>s1)
                    
  -- * adding if-then-else constructs
                    
  ITE b e1 e2     -> do (t1,s1) <- w b  $ env;
                        (t2,s2) <- w e1 . fmap (subst s1) $ env;
                        (t3,s3) <- w e2 . fmap (subst (s2<>s1)) $ env;
                        s4 <- u (subst (s3<>s2) t1) (TyCon "Bool");
                        s5 <- u (subst s4 t3) (subst (s4<>s3) t2);
                        return (subst (s5<>s4) t3, s5<>s4<>s3<>s2)
                    
  -- * adding product types
  
  Con _ n (Prod x y) -> do (t1,s1) <- w x $ env;
                           (t2,s2) <- w y . fmap (subst s1) $ env;
                           return (TyProd n (subst s2 t1) t2, s2<>s1)
    
  Des n e1 (UnProd x y e2) -> do (t1,s1) <- w e1 $ env;
                                 a <- fresh;
                                 b <- fresh;
                                 s2 <- u t1 (TyProd n a b);
                                 (t3,s3) <- w e2 . (y ~> b) . (x ~> a) . fmap (subst (s2<>s1)) $ env;
                                 return (t3,s3<>s2<>s1)
  
  
  
  