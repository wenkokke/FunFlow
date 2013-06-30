{-# LANGUAGE FlexibleInstances #-}

module FUN.CFA where

import FUN.Base
import Text.Printf (printf)

import Prelude hiding (mapM)

import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.List as L (union)

import Data.Monoid hiding ((<>))
import Data.Traversable (forM,mapM)

import Control.Monad (join)
import Control.Applicative hiding (empty)

import Control.Monad.Error (Error (..),ErrorT,runErrorT,throwError)
import Control.Monad.Supply (Supply, SupplyT, supply, evalSupply, evalSupplyT)
import Control.Monad.Trans (lift)

import Data.Set ( Set, empty, singleton, union )
import qualified Data.Set as Set

-- * For Pepijn ^^

type TyEnv = Env 

-- * Type definitions

type TVar = Name
type AVar = Name

data Ann 
  = AVar AVar
  deriving (Eq, Ord, Show)

data Type
  = TCon  TVar
  | TVar  TVar
  | TArr  Ann Type Type
  | TSum  TVar Type Type
  | TProd TVar Type Type
  deriving (Eq)
    
instance Show Type where
  show = showType False

showType :: Bool -> Type -> String
showType cp = let 
  showType' ty = 
    case ty of 
      (TCon  n    ) -> n
      (TVar  n    ) -> n
      (TArr  r a b) -> printf "%s -%s> %s" (wrap a) (printAnn r) (wrap b)
          where
          wrap ty@(TArr _ _ _) = printf "(%s)" (showType' ty)
          wrap ty             = showType' ty
          printAnn (AVar s) = if cp then s else ""
      (TSum n a b) -> printf "%s %s %s" n (wrap a) (wrap b)
          where
          wrap ty@(TProd _ _ _) = printf "(%s)" (showType' ty)
          wrap ty@(TSum  _ _ _) = printf "(%s)" (showType' ty)
          wrap ty@(TArr _ _ _)  = printf "(%s)" (showType' ty)
          wrap ty                = showType' ty
      (TProd n a b) -> printf "%s %s %s" n (wrap a) (wrap b)
          where
          wrap ty@(TProd _ _ _) = printf "(%s)" (showType' ty)
          wrap ty@(TSum  _ _ _) = printf "(%s)" (showType' ty)
          wrap ty@(TArr _ _ _)  = printf "(%s)" (showType' ty)
          wrap ty                = showType' ty
 in showType' 
-- * Algorithm W for Type Inference

-- |Runs algorithm W on a list of declarations, making each previous
--  declaration an available expression in the next.
runCFA :: [Decl] -> Either TypeError (Env, Set Constraint)
runCFA = refreshAll . withFreshVars . foldl addDecl (return (mempty, empty))
  where
  addDecl :: CFA (Env, Set Constraint) -> Decl-> CFA (Env, Set Constraint)
  addDecl r (Decl x e) = do (env, c0) <- r
                            (t, s1, c1) <- cfa e $ env
                            return (M.insert x t env, subst s1 c0 `union` c1)


-- |Provides an infinite stream of names to things in the @CFA@ monad,
--  reducing it to just an @Either@ value containing perhaps a TypeError.
withFreshVars :: CFA a -> Either TypeError a
withFreshVars x = evalSupply (evalSupplyT (runErrorT x) freshAVars) freshTVars
  where
  freshAVars = fmap show [0..]
  freshTVars = letters ++ numbers
    where
    letters = fmap (: []) ['a'..'z']
    numbers = fmap (('t' :) . show) [0..]

-- |Refreshes all entries in a type environment.
refreshAll :: Either TypeError (Env, Set Constraint) -> Either TypeError (Env, Set Constraint)
refreshAll env = do (env, c) <- env;
                    env <- mapM (withFreshVars . refresh) env
                    return (env, c {- TODO: refresh constraint sets, if needed? -} ) 

-- |Replaces every type variable with a fresh one.
refresh :: Type -> CFA Type
refresh t1 = do subs <- forM (ftv t1) $ \a ->
                          do b <- fresh;
                             return (M.singleton a b, M.empty)
                return (subst (mconcat subs) t1)

-- |Returns the set of free type variables in a type.
ftv :: Type -> [TVar]
ftv (TCon      _) = [ ]
ftv (TVar      n) = [n]
ftv (TArr  _ a b) = L.union (ftv a) (ftv b)
ftv (TSum  _ a b) = L.union (ftv a) (ftv b)
ftv (TProd _ a b) = L.union (ftv a) (ftv b)
  
type TySubst = (Map TVar Type, Map AVar Ann)

class Subst w where
  subst :: TySubst -> w -> w

  
-- |Substitutes a type for a type variable in a type.
instance Subst Type where
  subst m c@(TCon _)    = c
  subst m v@(TVar n)    = M.findWithDefault v n (fst m)
  subst m (TArr  v a b) = TArr (subst m v) (subst m a) (subst m b)
  subst m (TSum  n a b) = TSum  n (subst m a) (subst m b)
  subst m (TProd n a b) = TProd n (subst m a) (subst m b)

instance Subst Ann where
  subst m v@(AVar n) = M.findWithDefault v n (snd m)
  
instance Subst (Set Constraint) where
  subst m cs = flip Set.map cs $ \(Constraint v r) -> Constraint (subst m v) r
  
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

type CFA a = ErrorT TypeError (SupplyT AVar (Supply TVar)) a

-- |Occurs check for Robinson's unification algorithm.
occurs :: TVar -> Type -> Bool
occurs n t = n `elem` (ftv t)

-- |Unification as per Robinson's unification algorithm.
u :: Type -> Type -> CFA TySubst
u t1@(TCon a) t2@(TCon b)
  | a == b        = return mempty
  | otherwise     = throwError (CannotUnify t1 t2)
u (TArr (AVar p1) a1 b1) (TArr p2 a2 b2)
                  = do let s0 = (M.empty, M.singleton p1 p2)
                       s1 <- subst s0 a1 `u` subst s0 a2
                       s2 <- subst (s1 <> s0) b1 `u` subst (s1 <> s0) b2
                       return (s2 <> s1 <> s0)
u t1@(TProd n1 x1 y1) t2@(TProd n2 x2 y2)
                  = if n1 == n2
                    then do s1 <- x1 `u` x2;
                            s2 <- subst s1 y1 `u` subst s1 y2
                            return (s2 <> s1)
                    else do throwError (CannotUnify t1 t2)
u t1@(TSum n1 x1 y1) t2@(TSum n2 x2 y2)
                  = if n1 == n2
                    then do s1 <- x1 `u` x2;
                            s2 <- subst s1 y1 `u` subst s1 y2
                            return (s2 <> s1)
                    else do throwError (CannotUnify t1 t2)
u t1 t2@(TVar n)
  | n `occurs` t1 && t1 /= t2 = throwError (OccursCheck n t1)
  | otherwise     = return (M.singleton n t1, M.empty)
u t1@(TVar n) t2
  | n `occurs` t2 && t1 /= t2 = throwError (OccursCheck n t2)
  | otherwise     = return (M.singleton n t2, M.empty)
u t1 t2           = throwError (CannotUnify t1 t2)

typeOf :: Lit -> Type
typeOf (Bool    _) = TCon "Bool"
typeOf (Integer _) = TCon "Integer"

class Fresh t where
  fresh :: CFA t

instance Fresh Type where
  fresh = fmap TVar $ lift (lift supply)
  
instance Fresh Ann where
  fresh = fmap AVar $ lift supply

(~>) :: TVar -> Type -> Env -> Env
(~>) = M.insert

(<>) :: TySubst -> TySubst -> TySubst
(<>) m@(s2, a2) (s1, a1) = ( s2 `M.union` (subst m <$> s1)
                           , a2 `M.union` (subst m <$> a1)
                           )

data Constraint = Constraint Ann Label
  deriving (Eq, Ord, Show)
  
printFlow :: Map AVar (Set Label) -> String
printFlow m = 
  let prefix = "{\n"
      content = M.foldWithKey (\k a as -> "  " ++ k ++ " -> " ++ show a ++ "\n" ++ as) "" m
      suffix = "}"
  in prefix ++ content ++ suffix
  
organiseFlow :: Set Constraint -> Map AVar (Set Label)
organiseFlow = M.unionsWith (union) . map extractConstraint . S.toList where
  extractConstraint (Constraint v l) = case v of
                                          AVar r -> M.singleton r (S.singleton l)

  
($*) :: Applicative f => Ord a => Map a b -> a -> f b -> f b
f $* a = \d -> case M.lookup a f of
                    Just b  -> pure b
                    Nothing -> d

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip fmap

infixr 1 <&>

constraint :: Ann -> Label -> Set Constraint
constraint a l = singleton $ Constraint a l

-- |Algorithm W for type inference.
cfa :: Expr -> Env -> CFA (Type, TySubst, Set Constraint)
cfa exp env = case exp of
  Lit l           -> return ( typeOf l
                            , mempty
                            , empty
                            )
  
  Var x           -> do v <- (env $* x) $ throwError (UnboundVariable x)
                           
                        return ( v
                               , mempty
                               , empty
                               )
               
  Abs p x e       -> do a_x <- fresh;
                        b_0 <- fresh
                        
                        (t0, s0, c0) <- cfa e . (x ~> a_x) $ env
                        
                        return ( TArr b_0 (subst s0 a_x) t0
                               , s0
                               , c0 `union` constraint b_0 p
                               )

  -- * adding fixpoint operators
  
  Fix p f x e     -> do a_x <- fresh
                        a_0 <- fresh
                        b_0 <- fresh
                        
                        (t0, s0, c0) <- cfa e . (f ~> TArr b_0 a_x a_0) . (x ~> a_x) $ env
                        
                        s1 <- t0 `u` subst s0 a_0
                        
                        let b_1 = subst (s1 <> s0) b_0 

                        return ( TArr b_1 (subst (s1 <> s0) a_x) (subst s1 t0)
                               , s1 <> s0
                               , subst s1 c0 `union` constraint b_1 p
                               )

                        
  App f e         -> do (t1, s1, c1) <- cfa f $ env
                        (t2, s2, c2) <- cfa e . fmap (subst s1) $ env
                        
                        a <- fresh;
                        b <- fresh
                        
                        s3 <- subst s2 t1 `u` TArr b t2 a

                        return ( subst s3 a 
                               , s3 <> s2 <> s1
                               , subst (s3 <> s2) c1 `union` 
                                 subst  s3        c2
                               )
  
  Let x e1 e2     -> do (t1, s1, c1) <- cfa e1 $ env;
                        (t2, s2, c2) <- cfa e2 . (x ~> t1) . fmap (subst s1) $ env

                        return ( t2
                               , s2 <> s1
                               , subst s2 c1 `union` c2
                               )

                    
  -- * adding if-then-else constructs
                    
  ITE b e1 e2     -> do (t0, s0, c0) <- cfa b  $ env;
                        (t1, s1, c1) <- cfa e1 . fmap (subst s0) $ env
                        (t2, s2, c2) <- cfa e2 . fmap (subst (s1 <> s0)) $ env
                        
                        s3 <- subst (s2 <> s1) t0 `u` TCon "Bool"
                        s4 <- subst s3 t2 `u` subst (s3 <> s2) t1;

                        return ( subst (s4 <> s3) t2
                               , s4 <> s3 <> s2 <> s1 
                               , subst (s4 <> s3 <> s2 <> s1) c0 `union` 
                                 subst (s4 <> s3 <> s2)       c1 `union` 
                                 subst (s4 <> s3)             c2
                               )
                    
  -- * adding product types
  
  Con _ n x y     -> do (t1, s1, c1) <- cfa x $ env
                        (t2, s2, c2) <- cfa y . fmap (subst s1) $ env
 
                        return ( TProd n (subst s2 t1) t2
                               , s2 <> s1
                               , empty
                               )
  
  Des e1 n x y e2 -> do (t1, s1, c1) <- cfa e1 env
                        
                        a <- fresh
                        b <- fresh
                        
                        s2 <- t1 `u` TProd n a b
                        (t3, s3, c3) <- cfa e2 . (y ~> b) . (x ~> a) . fmap (subst (s2 <> s1)) $ env

                        return ( t3
                               , s3 <> s2 <> s1
                               , empty
                               )
