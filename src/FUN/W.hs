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
  = TyCon Name
  | TyVar Name
  | TyArr Type Type
  deriving (Eq)
  
instance Show Type where
  show (TyCon n)   = n
  show (TyVar n)   = n
  show (TyArr a b) = printf "%s -> %s" (show_parens a) (show_parens b)
    where
    show_parens :: Type -> String
    show_parens (TyCon n)   = n
    show_parens (TyVar n)   = n
    show_parens (TyArr a b) = printf "(%s -> %s)" (show a) (show b)

-- |Returns the set of free type variables in a type.
ftv :: Type -> Set Name
ftv (TyCon   _) = S.empty
ftv (TyVar   n) = S.singleton n
ftv (TyArr a b) = S.union (ftv a) (ftv b)
  
type TySubst
  = Map Name Type

-- |Substitutes a type for a type variable in a type.
subst :: TySubst -> Type -> Type
subst m c@(TyCon n) = c
subst m v@(TyVar n) = M.findWithDefault v n m
subst m (TyArr f a) = TyArr (subst m f) (subst m a)

type TyEnv
  = Map Name Type

-- |Representation for possible errors in algorithm W.
data WError
  = UnknownVariable Name      -- ^ thrown when unknown variable is encountered
  | OccursCheck     Name Type -- ^ thrown when occurs check in unify fails
  | CannotUnify     Type Type -- ^ thrown when types cannot be unified
  | OtherError      String    -- ^ stores miscellaneous errors
  | NoMsg                     -- ^ please don't be a jackass; don't use this
  deriving Eq

instance Error WError where
  noMsg       = NoMsg
  strMsg msg  = OtherError msg

instance Show WError where
  show (UnknownVariable n) = printf "Unknown variable %s" n
  show (CannotUnify   a b) = printf "Cannot unify %s with %s" (show a) (show b)
  show (OtherError    msg) = msg
  show (NoMsg            ) = "Dead."

type W a = ErrorT WError (Supply Name) a
type U a = Either WError a

-- |Occurs check for Robinson's unification algorithm.
occursIn :: Name -> Type -> Bool
occursIn n t = S.member n (ftv t)

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
  | n `occursIn` t  = return $ M.singleton n t
  | otherwise       = throwError $ OccursCheck n t
u (TyVar n) t
  | n `occursIn` t  = return $ M.singleton n t
  | otherwise       = throwError $ OccursCheck n t
u t1 t2
  = throwError $ CannotUnify t1 t2

-- |Types for literals.
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
  Lit l       -> return (typeOf l,mempty)
  Var n       -> case M.lookup n env of
                    Just  v -> return (v,mempty)
                    Nothing -> throwError (UnknownVariable n)
  Abs x e     -> do a <- fresh;
                    (t1,s1) <- w ((x ~> a) env,e);
                    return (TyArr (subst s1 a) t1,s1)
  App f e     -> do (t1,s1) <- w (env,f);
                    (t2,s2) <- w (fmap (subst s1) env,e);
                    a  <- fresh;
                    s3 <- u (subst s2 t1) (TyArr t2 a);
                    return (subst s3 a, mconcat [s3,s2,s1])
  Let x e1 e2 -> do (t1,s1) <- w (env,e1);
                    (t2,s2) <- w ((x ~> t1) (fmap (subst s1) env),e2);
                    return (t2, s2 <> s1)

                    














