module FUN.W where

import FUN.Base
import Text.Printf (printf)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Control.Monad.Error (Error (..),ErrorT,throwError)
import Control.Monad.Supply (Supply,supply)
import Control.Monad.Trans (lift)

data Type
  = TyCon  Name
  | TyVar  Name
  | TyArr  Type Type
  | TyProd Name Type Type
  deriving (Eq)
  
instance Show Type where
  show (TyCon  n    ) = n
  show (TyVar  n    ) = n
  show (TyArr    a b) = printf "%s -> %s" (show_parens a) (show_parens b)
    where
    show_parens ty@(TyArr _ _) = printf "(%s)" (show ty)
    show_parens ty             = show ty
  show (TyProd n a b) = printf "%s %s %s" n (show_parens a) (show_parens b)
    where
    show_parens ty@(TyProd _ _ _) = printf "(%s)" (show ty)
    show_parens ty                = show ty

-- |Returns the set of free type variables in a type.
ftv :: Type -> Set Name
ftv (TyCon      _) = S.empty
ftv (TyVar      n) = S.singleton n
ftv (TyArr    a b) = S.union (ftv a) (ftv b)
ftv (TyProd _ a b) = S.union (ftv a) (ftv b)
  
type TySubst
  = Map Name Type

-- |Substitutes a type for a type variable in a type.
subst :: TySubst -> Type -> Type
subst m c@(TyCon n) = c
subst m v@(TyVar n) = M.findWithDefault v n m
subst m (TyArr f a) = TyArr (subst m f) (subst m a)
--subst m (TyProd n a b)

type TyEnv
  = Map Name Type

-- |Representation for possible errors in algorithm W.
data WError
  = CannotDestruct  Type      -- ^ thrown when attempting to destruct a non-product
  | PatternError    Name Name -- ^ thrown when pattern matching on a different type
  | UnknownVariable Name      -- ^ thrown when unknown variable is encountered
  | OccursCheck     Name Type -- ^ thrown when occurs check in unify fails
  | CannotUnify     Type Type -- ^ thrown when types cannot be unified
  | OtherError      String    -- ^ stores miscellaneous errors
  | NoMsg                     -- ^ please don't be a jackass; don't use this
  deriving Eq

instance Error WError where
  noMsg       = NoMsg
  strMsg msg  = OtherError msg

instance Show WError where
  show (CannotDestruct   t) = printf "Cannot deconstruct expression of type %s" (show t)
  show (PatternError   a b) = printf "Cannot match pattern %s with %s" a b
  show (UnknownVariable  n) = printf "Unknown variable %s" n
  show (OccursCheck    n t) = printf "Occurs check fails: %s occurs in %s" n (show t)
  show (CannotUnify    a b) = printf "Cannot unify %s with %s" (show a) (show b)
  show (OtherError     msg) = msg
  show (NoMsg             ) = "nope"

type W a = ErrorT WError (Supply Name) a
type U a = Either WError a

-- |Occurs check for Robinson's unification algorithm.
occurs :: Name -> Type -> Bool
occurs n t = S.member n (ftv t)

-- |Unification as per Robinson's unification algorithm.
u :: Type -> Type -> W TySubst
u t1@(TyCon a) t2@(TyCon b)
  | a == b    = return $ mempty
  | otherwise = throwError $ CannotUnify t1 t2
u (TyArr a1 b1) (TyArr a2 b2)
  = do s1 <- u a1 a2
       s2 <- u (subst s1 b1) (subst s1 b2)
       return $ s2 <> s1
u t (TyVar n)
  | n `occurs` t  = throwError $ OccursCheck n t
  | otherwise     = return $ M.singleton n t
u (TyVar n) t
  | n `occurs` t  = throwError $ OccursCheck n t
  | otherwise     = return $ M.singleton n t
u t1 t2
  = throwError $ CannotUnify t1 t2

typeOf :: Lit -> Type
typeOf (Bool    _) = TyCon "Bool"
typeOf (Integer _) = TyCon "Integer"

fresh :: W Type
fresh = do x <- lift supply;
           return (TyVar x)
           
freshNames :: [Name]
freshNames = fmap (:[]) ['a'..'z']

(~>) :: Name -> Type -> TyEnv -> TyEnv
(~>) = M.insert
           
-- |Algorithm W for type inference.
w :: (TyEnv,Expr) -> W (Type,TySubst)
w (env,exp) = case exp of
  Lit l           -> return (typeOf l,mempty)
  
  Var n           -> case M.lookup n env of
                        Just  v -> return (v,mempty)
                        Nothing -> throwError (UnknownVariable n)
  
  Abs   x e       -> do a <- fresh;
                        (t1,s1) <- w ((x ~> a) env,e);
                        return (TyArr (subst s1 a) t1,s1)
  
  App f   e       -> do (t1,s1) <- w (env,f);
                        (t2,s2) <- w (fmap (subst s1) env,e);
                        a  <- fresh;
                        s3 <- u (subst s2 t1) (TyArr t2 a);
                        let u21 = fmap (subst s3) (s2<>s1);
                        return (subst s3 a, s3<>u21)
  
  Let x e1 e2     -> do (t1,s1) <- w (env,e1);
                        (t2,s2) <- w ((x ~> t1).fmap (subst s1) $ env,e2);
                        return (t2, s2<>s1)

  -- * adding fixpoint operators
  
  Fix f x e       -> do a <- fresh;
                        b <- fresh;
                        let g = TyArr a b;
                        (t1,s1) <- w ((f ~> g).(x ~> a) $ env,e);
                        s2 <- u t1 (subst s1 b);
                        let u1 = fmap (subst s2) s1
                        return (TyArr (subst (s2<>s1) a) (subst s2 t1), s2<>u1)
                    
  -- * adding if-then-else constructs
                    
  ITE b e1 e2     -> do (t1,s1) <- w (env,b);
                        (t2,s2) <- w (fmap (subst s1) env,e1);
                        (t3,s3) <- w (fmap (subst (s2<>s1)) env,e2);
                        -- TODO maybe apply subst over substs
                        s4 <- u (subst (s3<>s2) t1) (TyCon "Bool");
                        s5 <- u (subst s4 t3) (subst (s4<>s3) t2);
                        return (subst (s5<>s4) t3, s5<>u432)
                    
  -- * adding product types
  
  Con n x y       -> do (t1,s1) <- w (env,x);
                        (t2,s2) <- w (fmap (subst s1) env,y);
                        return (TyProd n t1 t2, s2<>s1)
                    
  Des e1 n x y e2 -> do (t1,s1) <- w (env,e1);
                        (TyProd m a b) <- checkType t1;
                        checkPattern n m;
                        (t2,s2) <- w ((y ~> b).(x ~> a).fmap (subst s1) $ env,e2);
                        return (t2,s2<>s1)
    where
    checkPattern n m
      | n == m    = return () 
      | otherwise = throwError $ PatternError n m
    
    checkType ty = case ty of
      TyProd _ _ _ -> return ty
      _            -> throwError $ CannotDestruct ty
  