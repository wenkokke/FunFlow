{-# LANGUAGE FlexibleInstances #-}

module FUN.CFA where

import FUN.Base
import Text.Printf (printf)

import Prelude hiding (mapM)

import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.List as L (union)

import Data.Monoid hiding ((<>), Sum (..) )
import Data.Traversable (forM,mapM)

import Control.Monad (join)
import Control.Applicative hiding (empty)

import Control.Monad.Error (Error (..),ErrorT,runErrorT,throwError)
import Control.Monad.Supply (Supply, SupplyT, supply, evalSupply, evalSupplyT)
import Control.Monad.Trans (lift)

import Data.Set ( Set, empty, singleton, union )
import qualified Data.Set as Set

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
  | TProd Ann Name Type Type
  | TSum  Ann Name Type Type
  | TUnit Ann Name
  deriving (Eq)
    
instance Show Type where
  show = showType False

showType :: Bool -> Type -> String
showType cp = 
  let printAnn (AVar s) = if cp then "{" ++ s ++ "}" else ""
      showType ty = case ty of 
        TCon  n     -> n
        TVar  n     -> n
        TArr  v a b -> printf "%s -%s> %s" (wrap a) (printAnn v) (wrap b)
            where
            wrap ty@(TArr _ _ _) = printf "(%s)" (showType ty)
            wrap ty              = showType ty
        TProd v nm a b -> printf "%s%s(%s, %s)" nm (printAnn v) (wrap a) (wrap b)
            where
            wrap ty@(TProd _ _ _ _) = printf "(%s)" (showType ty)
            wrap ty@(TSum  _ _ _ _) = printf "(%s)" (showType ty)
            wrap ty@(TArr _ _ _)    = printf "(%s)" (showType ty)
            wrap ty                 = showType ty
        TSum v nm a b -> printf "%s%s %s %s" nm (printAnn v) (wrap a) (wrap b)
            where
            wrap ty@(TProd _ _ _ _) = printf "(%s)" (showType ty)
            wrap ty@(TSum  _ _ _ _) = printf "(%s)" (showType ty)
            wrap ty@(TArr _ _ _)    = printf "(%s)" (showType ty)
            wrap ty                 = showType ty
        TUnit v nm -> printf "%s%s()" nm (printAnn v)
  in showType
-- * Algorithm W for Type Inference

-- |Runs algorithm W on a list of declarations, making each previous
--  declaration an available expression in the next.
runCFA :: [Decl] -> Either TypeError (Env, Set Constraint)
runCFA = refreshAll . withFreshVars . foldl addDecl (return (mempty, empty))
  where
  addDecl :: CFA (Env, Set Constraint) -> Decl-> CFA (Env, Set Constraint)
  addDecl r (Decl x e) = do (env, c0) <- r
                            (t, s1, c1) <- cfa e $ env
                            
                            let s2 = (M.empty, snd s1)
                                
                            return ( (M.insert x t . fmap (subst s2) $ fst env, snd env)
                                   , subst s1 c0 `union` c1
                                   )


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
refreshAll env = do ((env, w), c) <- env;
                    env <- mapM (withFreshVars . refresh) env
                    return ((env, w), c) 

-- |Replaces every type variable with a fresh one.
refresh :: Type -> CFA Type
refresh t1 = do subs <- forM (ftv t1) $ \a ->
                          do b <- fresh;
                             return (M.singleton a b, M.empty)
                return $ subst (mconcat subs) t1

-- |Returns the set of free type variables in a type.
ftv :: Type -> [TVar]
ftv (TCon  _)       = [ ]
ftv (TVar  n)       = [n]
ftv (TArr  _   a b) = L.union (ftv a) (ftv b)
ftv (TProd _ _ a b) = L.union (ftv a) (ftv b)
ftv (TSum  _ _ a b) = L.union (ftv a) (ftv b)
ftv (TUnit _ _)     = [ ]

-- |Returns the set of free annotation variables in a type.
fav :: Type -> [AVar]
fav (TCon      _) = [ ]
fav (TVar      _) = [ ]
fav (TArr  v   a b) = fav a `L.union` fav b `L.union` [case v of (AVar r) -> r]
fav (TProd v _ a b) = fav a `L.union` fav b `L.union` [case v of (AVar r) -> r]
fav (TSum  v _ a b) = fav a `L.union` fav b `L.union` [case v of (AVar r) -> r]
fav (TUnit v _)     = [case v of (AVar r) -> r]

type TyEnv = Map TVar Type
type AnnEnv = Map AVar Ann

type Env = (TyEnv, AnnEnv)

class Subst w where
  subst :: Env -> w -> w

  
-- |Substitutes a type for a type variable in a type.
instance Subst Type where
  subst m c@(TCon _)    = c
  subst m v@(TVar n)    = M.findWithDefault v n (fst m)
  subst m (TArr  v    a b) = TArr (subst m v) (subst m a) (subst m b)
  subst m (TProd v nm a b) = TProd (subst m v) nm (subst m a) (subst m b)
  subst m (TSum  v nm a b) = TSum  (subst m v) nm (subst m a) (subst m b)
  subst m (TUnit v nm)     = TUnit (subst m v) nm
  
instance Subst Ann where
  subst m v@(AVar n) = M.findWithDefault v n (snd m)
  
instance Subst (Set Constraint) where
  subst m cs = flip Set.map cs $ \(FlowConstraint nm v r) -> FlowConstraint nm (subst m v) r
  


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
u :: Type -> Type -> CFA Env
u t1@(TCon a) t2@(TCon b)
  | a == b        = return mempty
  | otherwise     = throwError (CannotUnify t1 t2)
u (TArr (AVar p1) a1 b1) (TArr p2 a2 b2)
                  = do let s0 = (M.empty, M.singleton p1 p2)
                       s1 <- subst s0 a1 `u` subst s0 a2
                       s2 <- subst (s1 <> s0) b1 `u` subst (s1 <> s0) b2
                       return (s2 <> s1 <> s0)
u t1@(TProd (AVar p1) n1 x1 y1) t2@(TProd p2 n2 x2 y2)
                  = if n1 == n2
                    then do let s0 = (M.empty, M.singleton p1 p2)
                            s1 <- subst s0 x1 `u` subst s0 x2;
                            s2 <- subst (s1 <> s0) y1 `u` subst (s1 <> s0) y2
                            return (s2 <> s1 <> s0)
                    else do throwError (CannotUnify t1 t2)
u t1@(TSum (AVar p1) n1 x1 y1) t2@(TSum p2 n2 x2 y2)
                  = if n1 == n2
                    then do let s0 = (M.empty, M.singleton p1 p2)
                            s1 <- subst s0 x1 `u` subst s0 x2;
                            s2 <- subst (s1 <> s0) y1 `u` subst (s1 <> s0) y2
                            return (s2 <> s1 <> s0)
                    else do throwError (CannotUnify t1 t2)
u t1@(TUnit (AVar p1) n1) t2@(TUnit p2 n2)
                  = if n1 == n2
                    then do return $ (M.empty, M.singleton p1 p2)
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
x ~> t = \(m, w) -> (M.insert x t m, w)

(<>) :: Env -> Env -> Env
(<>) m@(s2, a2) (s1, a1) = ( s2 `M.union` (subst m <$> s1)
                           , a2 `M.union` (subst m <$> a1)
                           )

data Constraint = FlowConstraint String Ann Label
  deriving (Eq, Ord, Show)
  
printFlow :: Map AVar (String, Set Label) -> String
printFlow m = 
  let prefix = "{\n"
      printCon (nm, v) = nm ++ "\t{ " ++ (foldr1 (\x xs -> x ++ ", " ++ xs) . S.toList $ v) ++ " }"
      content = M.foldWithKey (\k a as -> "  " ++ k ++ "\t~> " ++ printCon a ++ "\n" ++ as) "" m
      suffix = "}"
  in prefix ++ content ++ suffix
    
solveConstraints :: Set Constraint -> Map AVar (String, Set Label)
solveConstraints = M.unionsWith (\(nx, vx) (ny, vy) -> (mergeNames nx ny, vx `union` vy) ) . map extractConstraint . S.toList where
  mergeNames p q = let (np, cp) = span (/= '.') p
                       (nq, cq) = span (/= '.') q
                   in if np == nq
                         then if cp == cq
                                 then p
                                 else np ++ ".{" ++ tail cp ++ ", " ++ tail cq ++ "}"
                         else error $ "different constructors used to construct sum type (\"" ++ np ++ "\" vs. \"" ++ nq ++ "\")"
                    
  extractConstraint (FlowConstraint nm v l) = case v of
                                          AVar r -> M.singleton r (nm, S.singleton l)

  
($*) :: Applicative f => Ord a => Map a b -> a -> f b -> f b
f $* a = \d -> 
  case M.lookup a f of
    Just b  -> pure b
    Nothing -> d

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip fmap

infixr 1 <&>

constraint :: String -> Ann -> Label -> Set Constraint
constraint nm a l = singleton $ FlowConstraint nm a l

class Bifunctor w where
  bimap :: (a -> x) -> (b -> y) -> w a b -> w x y
  
instance Bifunctor (,) where
  bimap f g (a, b) = (f a, g b)
  
lmap f = bimap f id
rmap g = bimap id g

-- |Algorithm W for type inference.
cfa :: Expr -> Env -> CFA (Type, Env, Set Constraint)
cfa exp env = case exp of
  Lit l           -> return ( typeOf l
                            , mempty
                            , empty
                            )
  
  Var x           -> do v <- (fst env $* x) $ throwError (UnboundVariable x)
                           
                        return ( v
                               , mempty
                               , empty
                               )
               
  Abs pi x e      -> do a_x <- fresh
                        b_0 <- fresh
                       
                        (t0, s0, c0) <- cfa e . (x ~> a_x) $ env
                       
                        return ( TArr b_0 (subst s0 a_x) t0
                               , s0
                               , c0 `union` constraint "Abs" b_0 pi
                               )                               
                               
  -- * adding fixpoint operators
  
  Fix pi f x e    -> do a_x <- fresh
                        a_0 <- fresh
                        b_0 <- fresh
                        
                        (t0, s0, c0) <- cfa e . (f ~> TArr b_0 a_x a_0) . (x ~> a_x) $ env
                        
                        s1 <- t0 `u` subst s0 a_0
                        
                        let b_1 = subst (s1 <> s0) b_0 

                        return ( TArr b_1 (subst (s1 <> s0) a_x) (subst s1 t0)
                               , s1 <> s0
                               , subst s1 c0 `union` constraint "Fix" b_1 pi
                               )

                        
  App f e         -> do (t1, s1, c1) <- cfa f $ env
                        (t2, s2, c2) <- cfa e $ s1 <> env
                        
                        a <- fresh;
                        b <- fresh
                        
                        s3 <- subst s2 t1 `u` TArr b t2 a

                        return ( subst s3 a 
                               , s3 <> s2 <> s1
                               , subst (s3 <> s2) c1 `union` 
                                 subst  s3        c2
                               )
  
  Let x e1 e2     -> do (t1, s1, c1) <- cfa e1 $ env;
                        (t2, s2, c2) <- cfa e2 . (x ~> t1) $ s1 <> env

                        return ( t2
                               , s2 <> s1
                               , subst s2 c1 `union` c2
                               )

                    
  -- * adding if-then-else constructs
                    
  ITE b e1 e2     -> do (t0, s0, c0) <- cfa b  $ env;
                        (t1, s1, c1) <- cfa e1 $ s0 <> env
                        (t2, s2, c2) <- cfa e2 $ s1 <> s0 <> env
                        
                        s3 <- subst (s2 <> s1) t0 `u` TCon "Bool"
                        s4 <- subst s3 t2 `u` subst (s3 <> s2) t1;

                        return ( subst (s4 <> s3) t2
                               , s4 <> s3 <> s2 <> s1 
                               , subst (s4 <> s3 <> s2 <> s1) c0 `union` 
                                 subst (s4 <> s3 <> s2)       c1 `union` 
                                 subst (s4 <> s3)             c2
                               )
                               
  Con pi nm Unit         -> do b_0 <- fresh
    
                               return ( TUnit b_0 nm
                                      , mempty
                                      , constraint nm b_0 pi
                                      )
  -- * adding product types
  Con pi nm (Prod x y)   -> do (t1, s1, c1) <- cfa x $ env
                               (t2, s2, c2) <- cfa y $ s1 <> env
      
                               b_0 <- fresh
      
                               return ( TProd b_0 nm (subst s2 t1) t2
                                      , s2 <> s1
                                      , subst s2 c1 `union` c1 `union` constraint nm b_0 pi 
                                      )
  -- * adding sum types
  Con pi nm (Sum L t)   -> do (t1, s1, c1) <- cfa t $ env
                              t2 <- fresh
                              
                              b_0 <- fresh
                              
                              return ( TSum b_0 nm t1 t2
                                      , s1
                                      , c1 `union` constraint (nm ++ ".Left") b_0 pi
                                      )
  Con pi nm (Sum R t)   -> do (t2, s1, c1) <- cfa t $ env
                              t1 <- fresh
                              
                              b_0 <- fresh
                              
                              return ( TSum b_0 nm t1 t2
                                      , s1
                                      , c1 `union` constraint (nm ++ ".Right") b_0 pi
                                      )

  Des nm e1 (UnUnit e2)     -> do (t1, s1, c1) <- cfa e1 env
                                             
                                  b_0 <- fresh
                                             
                                  s2 <- t1 `u` TUnit b_0 nm
                                  
                                  (t3, s3, c3) <- cfa e2 $ s2 <> s1 <> env
                                  
                                  return ( t3
                                         , s3 <> s2 <> s1
                                         , c3 `union` c1
                                         )

  Des nm e1 (UnProd x y e2)   -> do (t1, s1, c1) <- cfa e1 env
                                  
                                    a_x <- fresh
                                    a_y <- fresh
                                    
                                    b_0 <- fresh
                                    
                                    s2 <- t1 `u` TProd b_0 nm a_x a_y
                                    (t3, s3, c3) <- cfa e2 . (y ~> a_y) . (x ~> a_x) $ s2 <> s1 <> env

                                    return ( t3
                                           , s3 <> s2 <> s1
                                           , subst (s3 <> s2) c1 `union` c3
                                           )
                                           
  Des nm e1 (UnSum (x, ex) (y, ey))     -> do (t1, s1, c1) <- cfa e1 env
                                             
                                              a_x <- fresh
                                              a_y <- fresh
                                              
                                              b_0 <- fresh
                                              
                                              s2 <- t1 `u` TSum b_0 nm a_x a_y
                                             
                                              (tx, s3, c3) <- cfa ex . (x ~> a_x) $ s2 <> s1 <> env
                                              (ty, s4, c4) <- cfa ey . (y ~> a_y) $ s3 <> s2 <> s1 <> env
                                             
                                              s5 <- tx `u` ty
                                             
                                              return ( subst s5 tx
                                                     , s5 <> s4 <> s3 <> s2 <> s1
                                                     , subst (s5 <> s4 <> s3 <> s2) c1 `union` 
                                                       subst (s5 <> s4)             c3 `union` 
                                                       subst  s5                    c4 
                                                     )
