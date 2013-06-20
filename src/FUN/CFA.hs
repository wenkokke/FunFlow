{-# LANGUAGE FlexibleInstances #-}

module FUN.CFA where

import FUN.Base
import Text.Printf (printf)

import Prelude hiding (mapM)

import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.List as L (union)

import Data.Monoid hiding ((<>))
import Data.Traversable (forM,mapM)

import Control.Monad (join)
import Control.Applicative hiding (empty)

import Control.Monad.Error (Error (..),ErrorT,runErrorT,throwError)
import Control.Monad.Supply (Supply,supply,evalSupply)
import Control.Monad.Trans (lift)

import Data.Set ( Set, empty, singleton, union )
import qualified Data.Set as Set

-- * For Pepijn ^^

type TyEnv = Env 

-- * Type definitions

type TVar = Name
type AVar = Name

data Annotation 
  = AVar AVar
  deriving (Eq, Ord, Show)
data Type
  = TyCon  TVar
  | TyVar  TVar
  | TyArr  Annotation Type Type
  | TySum  TVar Type Type
  | TyProd TVar Type Type
  deriving (Eq)
  
instance Show Type where
  show (TyCon  n    ) = n
  show (TyVar  n    ) = n
  show (TyArr  r a b) = printf "%s -%s> %s" (wrap a) printAnnotation (wrap b)
    where
    wrap ty@(TyArr _ _ _) = printf "(%s)" (show ty)
    wrap ty             = show ty
    printAnnotation = if False then "(" ++ show r ++ ")" else ""
  show (TySum n a b) = printf "%s %s %s" n (wrap a) (wrap b)
    where
    wrap ty@(TyProd _ _ _) = printf "(%s)" (show ty)
    wrap ty@(TySum  _ _ _) = printf "(%s)" (show ty)
    wrap ty@(TyArr _ _ _)   = printf "(%s)" (show ty)
    wrap ty                = show ty
  show (TyProd n a b) = printf "%s %s %s" n (wrap a) (wrap b)
    where
    wrap ty@(TyProd _ _ _) = printf "(%s)" (show ty)
    wrap ty@(TySum  _ _ _) = printf "(%s)" (show ty)
    wrap ty@(TyArr _ _ _)  = printf "(%s)" (show ty)
    wrap ty                = show ty
    
-- * Algorithm W for Type Inference

-- |Runs algorithm W on a list of declarations, making each previous
--  declaration an available expression in the next.
runCFA :: [Decl] -> Either TypeError Env
runCFA = refreshAll . withFreshTVars . foldl addDecl (return mempty)
  where
  addDecl :: W Env -> Decl-> W Env
  addDecl env (Decl x e) = do env <- env;
                              (t,_, _) <- cfa e $ env
                              return (M.insert x t env)

-- |Provides an infinite stream of names to things in the @W@ monad,
--  reducing it to just an @Either@ value containing perhaps a TypeError.
withFreshTVars :: W a -> Either TypeError a
withFreshTVars x = evalSupply (runErrorT x) freshTVars
  where
  freshTVars = letters ++ numbers
    where
    letters = fmap (: []) ['a'..'z']
    numbers = fmap (('t' :) . show) [0..]
    
-- |Refreshes all entries in a type environment.
refreshAll :: Either TypeError Env -> Either TypeError Env
refreshAll env = do env <- env; mapM (withFreshTVars . refresh) env

-- |Replaces every type variable with a fresh one.
refresh :: Type -> W Type
refresh t1 = do subs <- forM (ftv t1)
                        $ \a ->
                          do b <- fresh;
                             return (M.singleton a b, M.empty)
                return (subst (mconcat subs) t1)

-- |Returns the set of free type variables in a type.
ftv :: Type -> [TVar]
ftv (TyCon      _) = [ ]
ftv (TyVar      n) = [n]
ftv (TyArr  _ a b) = L.union (ftv a) (ftv b)
ftv (TySum  _ a b) = L.union (ftv a) (ftv b)
ftv (TyProd _ a b) = L.union (ftv a) (ftv b)
  
type TySubst = (Map TVar Type, Map AVar Annotation)

class Subst w where
  subst :: TySubst -> w -> w

-- |Substitutes a type for a type variable in a type.
instance Subst Type where
  subst m c@(TyCon _)    = c
  subst m v@(TyVar n)    = M.findWithDefault v n (fst m)
  subst m (TyArr v@(AVar n)  a b) = TyArr ( M.findWithDefault v n (snd m) ) (subst m a) (subst m b)
  subst m (TySum  n a b) = TySum  n (subst m a) (subst m b)
  subst m (TyProd n a b) = TyProd n (subst m a) (subst m b)

instance Subst Annotation where
  subst m v@(AVar n) = M.findWithDefault v n (snd m)
  
instance Subst (Set Constraint) where
  subst m cs = flip Set.map cs $ \t ->
    case t of 
         Constraint v@(AVar n) r -> Constraint ( M.findWithDefault v n (snd m) ) r
  
type Env = Map TVar Type

-- |Representation for possible errors in algorithm W.
data TypeError
  = CannotDestruct  Type      -- ^ thrown when attempting to destruct a non-product
  | PatternError    TVar TVar -- ^ thrown when pattern matching on a different type
  | UnboundVariable TVar      -- ^ thrown when unknown variable is encountered
  | OccursCheck     TVar Type -- ^ thrown when occurs check in unify fails
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

type W a = ErrorT TypeError (Supply TVar) a

-- |Occurs check for Robinson's unification algorithm.
occurs :: TVar -> Type -> Bool
occurs n t = n `elem` (ftv t)

-- |Unification as per Robinson's unification algorithm.
u :: Type -> Type -> W TySubst
u t1@(TyCon a) t2@(TyCon b)
  | a == b        = return mempty
  | otherwise     = throwError (CannotUnify t1 t2)
u (TyArr (AVar p1) a1 b1) (TyArr p2 a2 b2)
                  = do let s0 = (M.empty, M.singleton p1 p2)
                       s1 <- subst s0 a1 `u` subst s0 a2
                       s2 <- subst (s1 <> s0) b1 `u` subst (s1 <> s0) b2
                       return (s2 <> s1 <> s0)
u t1@(TyProd n1 x1 y1) t2@(TyProd n2 x2 y2)
                  = if n1 == n2
                    then do s1 <- x1 `u` x2;
                            s2 <- subst s1 y1 `u` subst s1 y2
                            return (s2 <> s1)
                    else do throwError (CannotUnify t1 t2)
u t1@(TySum n1 x1 y1) t2@(TySum n2 x2 y2)
                  = if n1 == n2
                    then do s1 <- x1 `u` x2;
                            s2 <- subst s1 y1 `u` subst s1 y2
                            return (s2 <> s1)
                    else do throwError (CannotUnify t1 t2)
u t1 (TyVar n)
  | n `occurs` t1 = throwError (OccursCheck n t1)
  | otherwise     = return (M.singleton n t1, M.empty)
u (TyVar n) t2
  | n `occurs` t2 = throwError (OccursCheck n t2)
  | otherwise     = return (M.singleton n t2, M.empty)
u t1 t2           = throwError (CannotUnify t1 t2)

typeOf :: Lit -> Type
typeOf (Bool    _) = TyCon "Bool"
typeOf (Integer _) = TyCon "Integer"

class Fresh t where
  fresh :: W t

instance Fresh Type where
  fresh = fmap (\t -> TyVar t) $ lift supply


instance Fresh Annotation where
  fresh = fmap (\t -> AVar $ '%' : t) $ lift supply



(~>) :: TVar -> Type -> Env -> Env
(~>) = M.insert

(<>) :: TySubst -> TySubst -> TySubst
(<>) (s2, a2) (s1, a1) = ( M.union s2 (fmap (subst (s2, M.empty)) s1)
                         , M.union a2 a1 {- is this enough? -}
                         )
type Point = String

data Constraint = Constraint Annotation Point
  deriving (Eq, Ord)
  
($*) :: Applicative f => Ord a => Map a b -> a -> f b -> f b
f $* a = \d -> case M.lookup a f of
                    Just b  -> pure b
                    Nothing -> d

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip fmap

infixr 1 <&>

-- |Algorithm W for type inference.
cfa :: Expr -> Env -> W (Type, TySubst, Set Constraint)
cfa exp env = case exp of
  Lit l           -> return (typeOf l, mempty, empty)
  
  Var x           -> let notFoundError = throwError (UnboundVariable x)
                     in (env $* x) notFoundError <&> \v -> (v, mempty, empty)
               
  Abs _ x e       -> do a_x <- fresh;
                        (t0, s0, c0) <- cfa e . (x ~> a_x) $ env
                        b_0 <- fresh
                        let constraints = c0 `union` singleton (Constraint b_0 undefined)
                        return (TyArr b_0 (subst s0 a_x) t0, s0, constraints)

  -- * adding fixpoint operators
  
  Fix _ f x e     -> do a_x <- fresh
                        a_0 <- fresh
                        b_0 <- fresh
                        (t0, s0, c0) <- cfa e . (f ~> TyArr b_0 a_x a_0) . (x ~> a_x) $ env
                        s1 <- t0 `u` subst s0 a_0
                        let b1 = subst (s1 <> s0) b_0 
                            constraints = subst s1 c0 `union` singleton (Constraint b1 undefined)
                        return (TyArr b1 (subst (s1 <> s0) a_x) (subst s1 t0), s1 <> s0, constraints)

                        
  App f e         -> do (t1, s1, c1) <- cfa f $ env
                        (t2, s2, c2) <- cfa e . fmap (subst s1) $ env
                        a <- fresh;
                        b <- fresh
                        s3 <- subst s2 t1 `u` TyArr b t2 a
                        let constraints = subst (s3 <> s2) c1 `union` subst s3 c2 
                        return (subst s3 a, s3 <> s2 <> s1, constraints)
  
  Let x e1 e2     -> do (t1, s1, c1) <- cfa e1 $ env;
                        (t2, s2, c2) <- cfa e2 . (x ~> t1) . fmap (subst s1) $ env
                        let constraints = subst s2 c1 `union` c2
                        return (t2, s2 <> s1, constraints)

                    
  -- * adding if-then-else constructs
                    
  ITE b e1 e2     -> do (t0, s0, c0) <- cfa b  $ env;
                        (t1, s1, c1) <- cfa e1 . fmap (subst s0) $ env
                        (t2, s2, c2) <- cfa e2 . fmap (subst (s1 <> s0)) $ env
                        s3 <- subst (s2 <> s1) t0 `u` TyCon "Bool"
                        s4 <- subst s3 t2 `u` subst (s3 <> s2) t1;
                        let constraints = subst (s4 <> s3 <> s2 <> s1) c0 `union` subst (s4 <> s3 <> s2) c1 `union` subst (s4 <> s3) c2
                        return (subst (s4 <> s3) t2, s4 <> s3 <> s2 <> s1, constraints)
                    
  -- * adding product types
  
  Con _ n x y     -> do (t1, s1, c1) <- cfa x $ env
                        (t2, s2, c2) <- cfa y . fmap (subst s1) $ env
                        let constraints = empty
                        return (TyProd n (subst s2 t1) t2, s2 <> s1, constraints)
  
  Des e1 n x y e2 -> do (t1, s1, c1) <- cfa e1 env
                        a <- fresh
                        b <- fresh
                        s2 <- t1 `u` TyProd n a b
                        (t3, s3, c3) <- cfa e2 . (y ~> b) . (x ~> a) . fmap (subst (s2 <> s1)) $ env
                        let constraints = empty
                        return (t3, s3 <> s2 <> s1, constraints)
