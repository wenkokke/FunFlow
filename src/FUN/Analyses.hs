{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module FUN.Analyses where

import FUN.Base
import FUN.Labeling
import FUN.Analyses.Flow
import FUN.Analyses.Measure
import FUN.Analyses.Utils

import Prelude hiding (mapM)

import Debug.Trace (traceShow)

import Data.Monoid hiding ( Sum )

import Control.Applicative ((<$>))
import Control.Monad (join, foldM)
import Control.Monad.Error (Error (..),ErrorT,runErrorT,throwError)
import Control.Monad.Supply (Supply, SupplyT, supply, evalSupply, evalSupplyT)
import Control.Monad.Trans (lift)

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set ( Set, empty, union )
import qualified Data.Set as S
import qualified Data.List as L (union)
import Data.Traversable (forM,mapM)

import Text.Printf (printf)

prelude :: Analysis (Env, [Decl])
prelude = if False then return (mempty, []) else
  let id = Abs noLabel "x" (Var "x")
      predefs =
        [ ("asKelvin",  id, \v -> TArr v (TInt SNil BNil) (TInt (SCon "Kelvin" )  BNil))
        , ("asCelcius", id, \v -> TArr v (TInt SNil BNil) (TInt (SCon "Kelvin" ) (BCon "Freezing")))
        , ("asFeet",    id, \v -> TArr v (TInt SNil BNil) (TInt (SCon "Feet"   )  BNil))
        , ("asMeters",  id, \v -> TArr v (TInt SNil BNil) (TInt (SCon "Meter"  )  BNil))
        , ("asDollars", id, \v -> TArr v (TInt SNil BNil) (TInt (SCon "Dollar" )  BNil))
        , ("asEuros",   id, \v -> TArr v (TInt SNil BNil) (TInt (SCon "Euro"   )  BNil))
        , ("asSeconds", id, \v -> TArr v (TInt SNil BNil) (TInt (SCon "Seconds")  BNil))
        ]
  in do ps <- mapM (\(nm, e, f) -> do v <- fresh;
                                      return ( (nm, f v), Decl nm e)) $ predefs;
        let (env, ds) = unzip ps;
        return (Env (M.fromList env) emptyExtendedEnv, ds)

-- * Type definitions

-- |Type variables
type TVar = String

data Type
  = TVar  TVar
  | TBool
  | TInt  Scale Base
  | TArr  Flow Type Type
  | TProd Flow Name Type Type
  | TSum  Flow Name Type Type
  | TUnit Flow Name
  deriving (Eq)

instance Show Type where
  show = showType False

showType :: Bool -> Type -> String
showType cp =
  let printAnn (FVar s) = if cp then "{" ++ s ++ "}" else ""
      showType ty = case ty of
        TBool -> "Bool"
        TInt s b -> "Integer" ++ showScaleBase where
          showScaleBase = if s == SNil
                             then "" else
                          if b == BNil
                             then "{" ++ show s ++ "}"
                             else "{" ++ show s ++ "@" ++ show b ++ "}"
        TVar n -> n
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

-- |Returns the set of free type variables in a type.
ftv :: Type -> [TVar]
ftv TBool           = [ ]
ftv (TInt _ _)      = [ ]
ftv (TVar  n)       = [n]
ftv (TArr  _   a b) = L.union (ftv a) (ftv b)
ftv (TProd _ _ a b) = L.union (ftv a) (ftv b)
ftv (TSum  _ _ a b) = L.union (ftv a) (ftv b)
ftv (TUnit _ _)     = [ ]

-- |Types of primitives.
typeOf :: Lit -> Type
typeOf (Bool _) = TBool
typeOf (Integer s b _) = TInt s b

-- |Representation for possible errors in algorithm W.
data TypeError
  = CannotDestruct  Type      -- ^ thrown when attempting to destruct a non-product
  | PatternError    TVar TVar -- ^ thrown when pattern matching on a different type
  | UnboundVariable TVar      -- ^ thrown when unknown variable is encountered
  | OccursCheck     TVar Type -- ^ thrown when occurs check in unify fails
  | CannotUnify     Type Type -- ^ thrown when types cannot be unified
  | OtherError      String    -- ^ stores miscellaneous errors
  | MeasureError    String
  deriving Eq

instance Error TypeError where
  noMsg       = OtherError "no message"
  strMsg msg  = OtherError msg

instance Show TypeError where
  show (CannotDestruct   t) = printf "Cannot deconstruct expression of type %s" (show t)
  show (PatternError   a b) = printf "Cannot match pattern %s with %s" a b
  show (UnboundVariable  n) = printf "Unknown variable %s" n
  show (OccursCheck    n t) = printf "Occurs check fails: %s occurs in %s" n (show t)
  show (CannotUnify    a b) = printf "Cannot unify %s with %s" (show a) (show b)
  show (OtherError     msg) = msg
  show (MeasureError     s) = "Unit of Measure Error: " ++ s

type Analysis a = ErrorT TypeError (SupplyT FVar (Supply TVar)) a

(~>) :: TVar -> Type -> Env -> Env
x ~> t = \(Env m w) -> Env (M.insert x t m) w


instance Monoid Env where                    
  m@(Env s2 a2) `mappend` (Env s1 a1) = Env (s2 `M.union` (subst m <$> s1)) $
                                          ExtendedEnv {
                                            flowMap  = flowMap  a2 `M.union` (subst m <$> flowMap  a1),
                                            scaleMap = scaleMap a2 `M.union` (subst m <$> scaleMap a1),
                                            baseMap  = baseMap  a2 `M.union` (subst m <$> baseMap  a1)
                                          }
                                  
  mempty = Env M.empty emptyExtendedEnv

-- * Algorithm W for Type Inference

-- |Runs Algorithm W on a list of declarations, making each previous
--  declaration an available expression in the next.
analyseAll :: [Decl] -> Either TypeError (Env, Prog, Set Constraint)
analyseAll ds =
  let addDecl :: (Env, Set Constraint) -> Decl-> Analysis (Env, Set Constraint)
      addDecl (env, c0) (Decl x e) = do (t, s1, c1) <- analyse e $ env

                                        let s2 = Env M.empty (getExtended s1)

                                        return ( Env (M.insert x t . fmap (subst s2) $ getPrimary env) (getExtended env)
                                               , subst s1 c0 `union` c1
                                               )

  in refreshAll . withFreshVars $ do (env, lib) <- prelude

                                     let (labeledLib, labeledDecls) = runLabel $ (lib, ds)

                                     (env, c0) <- foldM addDecl (env, empty) $ labeledDecls
                                     
                                     -- extract the scale constraints
                                     let sc0  = extractScaleConstraints c0
                                     
                                     -- do a first run of constraint solving
                                     let ss1  = solveScaleConstraints sc0
                                     let env1 = subst ss1 env
                                     let sc1  = S.filter isValidScaleConstraint . subst ss1 $ sc0
                                     
                                     -- do a second run of constraint solving
                                     let ss2  = solveScaleConstraints sc1
                                     let env2 = subst ss2 env
                                     let sc2  = S.filter isValidScaleConstraint . subst ss2 $ sc1
                                     
                                     -- update the final constraint set
                                     let c2   = subst ss2 c0
                                     
                                     return (env2, Prog $ (labeledLib ++ labeledDecls), c2)

-- |Runs the Algorithm W inference for types, control flow and measures.
analyse :: Expr -> Env -> Analysis (Type, Env, Set Constraint)
analyse exp env = case exp of
  Lit l           -> return ( typeOf l
                            , mempty
                            , empty
                            )

  Var x           -> do v <- (getPrimary env $* x) $ throwError (UnboundVariable x)

                        return ( v
                               , mempty
                               , empty
                               )

  Abs pi x e      -> do a_x <- fresh
                        b_0 <- fresh

                        (t0, s0, c0) <- analyse e . (x ~> a_x) $ env

                        return ( TArr b_0 (subst s0 a_x) t0
                               , s0
                               , c0 `union` flowConstraint "Abs" b_0 pi
                               )

  -- * adding fixpoint operators

  Fix pi f x e    -> do a_x <- fresh
                        a_0 <- fresh
                        b_0 <- fresh

                        (t0, s0, c0) <- analyse e . (f ~> TArr b_0 a_x a_0) . (x ~> a_x) $ env

                        s1 <- t0 `u` subst s0 a_0

                        let b_1 = subst (s1 <> s0) b_0

                        return ( TArr b_1 (subst (s1 <> s0) a_x) (subst s1 t0)
                               , s1 <> s0
                               , subst s1 c0 `union` flowConstraint "Fix" b_1 pi
                               )


  App f e         -> do (t1, s1, c1) <- analyse f $ env
                        (t2, s2, c2) <- analyse e . subst s1 $ env

                        a <- fresh;
                        b <- fresh

                        s3 <- subst s2 t1 `u` TArr b t2 a

                        return ( subst s3 a
                               , s3 <> s2 <> s1
                               , subst (s3 <> s2) c1 `union`
                                 subst  s3        c2
                               )

  Let x e1 e2     -> do (t1, s1, c1) <- analyse e1 $ env;
                        (t2, s2, c2) <- analyse e2 . (x ~> t1) . subst s1 $ env

                        return ( t2
                               , s2 <> s1
                               , subst s2 c1 `union` c2
                               )


  -- * adding if-then-else constructs

  ITE b e1 e2     -> do (t0, s0, c0) <- analyse b $ env;
                        (t1, s1, c1) <- analyse e1 . subst s0 $ env
                        (t2, s2, c2) <- analyse e2 . subst (s1 <> s0) $ env

                        s3 <- subst (s2 <> s1) t0 `u` TBool
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
                                      , flowConstraint nm b_0 pi
                                      )
  -- * adding product types
  Con pi nm (Prod x y)   -> do (t1, s1, c1) <- analyse x $ env
                               (t2, s2, c2) <- analyse y . subst s1 $ env

                               b_0 <- fresh

                               return ( TProd b_0 nm (subst s2 t1) t2
                                      , s2 <> s1
                                      , subst s2 c1 `union`
                                                 c1 `union` flowConstraint nm b_0 pi
                                      )
  -- * adding sum types
  Con pi nm (Sum L t)   -> do (t1, s1, c1) <- analyse t $ env
                              t2 <- fresh

                              b_0 <- fresh

                              return ( TSum b_0 nm t1 t2
                                      , s1
                                      , c1 `union` flowConstraint (nm ++ ".Left") b_0 pi
                                      )
  Con pi nm (Sum R t)   -> do (t2, s1, c1) <- analyse t $ env
                              t1 <- fresh

                              b_0 <- fresh

                              return ( TSum b_0 nm t1 t2
                                      , s1
                                      , c1 `union` flowConstraint (nm ++ ".Right") b_0 pi
                                      )

  Des nm e1 (UnUnit e2)     -> do (t1, s1, c1) <- analyse e1 $ env

                                  b_0 <- fresh

                                  s2 <- t1 `u` TUnit b_0 nm

                                  (t3, s3, c3) <- analyse e2 . subst (s2 <> s1) $ env

                                  return ( t3
                                         , s3 <> s2 <> s1
                                         , subst (s3 <> s2) c1 `union` c3
                                         )

  Des nm e1 (UnProd x y e2)   -> do (t1, s1, c1) <- analyse e1 $ env

                                    a_x <- fresh
                                    a_y <- fresh

                                    b_0 <- fresh

                                    s2 <- t1 `u` TProd b_0 nm a_x a_y
                                    (t3, s3, c3) <- analyse e2 . (y ~> a_y) . (x ~> a_x) . subst (s2 <> s1) $ env

                                    return ( t3
                                           , s3 <> s2 <> s1
                                           , subst (s3 <> s2) c1 `union` c3
                                           )

  Des nm e1 (UnSum (x, ex) (y, ey))     -> do (t1, s1, c1) <- analyse e1 $ env

                                              a_x <- fresh
                                              a_y <- fresh

                                              b_0 <- fresh

                                              s2 <- t1 `u` TSum b_0 nm a_x a_y

                                              (tx, s3, c3) <- analyse ex . (x ~> a_x) . subst (s2 <> s1) $ env
                                              (ty, s4, c4) <- analyse ey . (y ~> a_y) . subst (s3 <> s2 <> s1) $ env

                                              s5 <- tx `u` ty

                                              return ( subst s5 tx
                                                     , s5 <> s4 <> s3 <> s2 <> s1
                                                     , subst (s5 <> s4 <> s3 <> s2) c1 `union`
                                                       subst (s5 <> s4)             c3 `union`
                                                       subst  s5                    c4
                                                     )

  Oper op x y -> do rx <- fresh
                    bx <- fresh

                    ry <- fresh
                    by <- fresh

                    (t1, s1, c1) <- analyse x $ env
                    s2 <- t1 `u` TInt rx bx


                    (t3, s3, c3) <- analyse y . subst (s2 <> s1) $ env
                    s4 <- t3 `u` TInt ry by

                    rz <- fresh
                    bz <- fresh

                    let c0 = case op of
                          Add -> scaleEquality [rx, ry, rz]            `union` selectBase   (bx, by) bz
                          Sub -> scaleEquality [rx, ry, rz]            `union` preserveBase (bx, by) bz
                          Mul -> scaleEquality [rz, (SMul rx ry)]      `union` baseEquality [bx, by, bz, BNil]
                          Div -> scaleEquality [rz, SMul rx (SInv ry)] `union` baseEquality [bx, by, bz, BNil]


                    return ( TInt rz bz
                           , s4 <> s3 <> s2 <> s1
                           , subst (s4 <> s3 <> s2 <> s1) c0 `union`
                             subst (s4 <> s3 <> s2)       c1 `union`
                             subst  s4                    c3
                           )

-- * Fresh Names

-- |Provides an infinite stream of names to things in the @Analysis@ monad,
--  reducing it to just an @Either@ value containing perhaps a TypeError.
withFreshVars :: Analysis a -> Either TypeError a
withFreshVars x = evalSupply (evalSupplyT (runErrorT x) freshAVars) freshTVars
  where
  freshAVars = fmap show [0..]
  freshTVars = letters ++ numbers
    where
    letters = fmap (: []) ['a'..'z']
    numbers = fmap (('t' :) . show) [0..]

-- |Refreshes all entries in a type environment.
refreshAll :: Either TypeError (Env, Prog, Set Constraint) -> Either TypeError (Env, Prog, Set Constraint)
refreshAll env = do (env, p, c) <- env;
                    m <- mapM (withFreshVars . refresh) $ getPrimary env
                    return (Env m $ getExtended env, p, c)

-- |Replaces every type variable with a fresh one.
refresh :: Type -> Analysis Type
refresh t1 = do subs <- forM (ftv t1) $ \a ->
                          do b <- (fresh :: Analysis Type)
                             return $ singleton (a, b)
                return $ subst (mconcat subs :: Env) t1

class Fresh t where
  fresh :: Analysis t

instance Fresh Type where
  fresh = fmap TVar $ lift (lift supply)

instance Fresh Flow where
  fresh = fmap FVar $ lift supply

instance Fresh Scale where
  fresh = fmap SVar $ lift supply

instance Fresh Base where
  fresh = fmap BVar $ lift supply
                                     
-- * Constraints

data Constraint
  = FlowConstraint  FlowConstraint
  | ScaleConstraint ScaleConstraint
  | BaseConstraint  BaseConstraint
    deriving (Eq, Ord, Show)

scaleEquality :: [Scale] -> Set Constraint
scaleEquality = S.singleton . ScaleConstraint . ScaleEquality . S.fromList

baseEquality :: [Base] -> Set Constraint
baseEquality = S.singleton . BaseConstraint . BaseEquality . S.fromList

selectBase :: (Base, Base) -> Base -> Set Constraint
selectBase xy z = S.singleton $ BaseConstraint $ BaseSelection xy z

flowConstraint :: String -> Flow -> Label -> Set Constraint
flowConstraint nm a l = singleton $ FlowConstraint $ Flow nm a l

preserveBase :: (Base, Base) -> Base -> Set Constraint
preserveBase xy z = S.singleton $ BaseConstraint $ BasePreservation xy z

extractFlowConstraints :: Set Constraint -> Set FlowConstraint
extractFlowConstraints = unionMap findFlows where
  findFlows (FlowConstraint r)      = S.singleton r
  findFlows _                       = S.empty

extractScaleConstraints :: Set Constraint -> Set ScaleConstraint
extractScaleConstraints = unionMap findScales where
    findScales (ScaleConstraint ss) = S.singleton ss
    findScales _                    = S.empty

extractBaseConstraints :: Set Constraint -> Set BaseConstraint
extractBaseConstraints = unionMap findBases where
  findBases (BaseConstraint bs) = S.singleton bs
  findBases _                   = S.empty
                    
-- * Environments

data Env = Env
  { getPrimary  :: (Map TVar Type)
  , getExtended :: ExtendedEnv
  }

data ExtendedEnv = ExtendedEnv
  { flowMap  :: Map FVar Flow
  , scaleMap :: Map SVar Scale
  , baseMap  :: Map BVar Base
  } deriving Show
  
emptyExtendedEnv = ExtendedEnv {
  flowMap  = M.empty,
  scaleMap = M.empty,
  baseMap  = M.empty
}
                                     
-- * Extend Substitutions to @Env@

-- |Substitutes a type for a type variable in a type.
instance Subst Env Type where
  subst m TBool = TBool
  subst m r@(TInt s b)     = TInt  (subst m s) (subst m b)
  subst m v@(TVar n)       = M.findWithDefault v n (getPrimary m)
  subst m (TArr  v    a b) = TArr  (subst m v) (subst m a) (subst m b)
  subst m (TProd v nm a b) = TProd (subst m v) nm (subst m a) (subst m b)
  subst m (TSum  v nm a b) = TSum  (subst m v) nm (subst m a) (subst m b)
  subst m (TUnit v nm)     = TUnit (subst m v) nm

instance Subst Env Env where
  subst m (Env r w) = Env (fmap (subst m) r) w

instance Subst Env Constraint where
  subst m (FlowConstraint r)   = FlowConstraint $ subst m r
  subst m (ScaleConstraint ss) = ScaleConstraint $ subst m ss
  subst m (BaseConstraint ss)  = BaseConstraint $ subst m ss
  
instance Subst Env Flow where
  subst e = subst (flowMap $ getExtended e)

instance Subst Env Scale where
  subst e = subst (scaleMap $ getExtended e)

instance Subst Env Base where
  subst e = subst (baseMap $ getExtended e)
  
instance Subst SSubst Env where
  subst s (Env p e) = Env (subst (injectSSubst s mempty) p) e
  
instance Subst SSubst Constraint where
  subst s = subst (injectSSubst s mempty)

injectSSubst :: SSubst -> Env -> Env
injectSSubst (SSubst m) e = Env (getPrimary e) ((getExtended e) { scaleMap = m })

-- * Unifications

-- |Unification as per Robinson's unification algorithm.
u :: Type -> Type -> Analysis Env
u TBool TBool = return $ mempty
u (TInt r1 b1) (TInt r2 b2)
                   = do s0 <- unifyScale r1 r2
                        s1 <- unifyBase b1 b2
                        return (s1 <> s0)
u (TArr (FVar p1) a1 b1) (TArr p2 a2 b2)
                  = do let s0 = singleton (p1, p2)
                       s1 <- subst s0 a1 `u` subst s0 a2
                       s2 <- subst (s1 <> s0) b1 `u` subst (s1 <> s0) b2
                       return (s2 <> s1 <> s0)
u t1@(TProd (FVar p1) n1 x1 y1) t2@(TProd p2 n2 x2 y2)
                  = if n1 == n2
                    then do let s0 = singleton (p1, p2)
                            s1 <- subst s0 x1 `u` subst s0 x2;
                            s2 <- subst (s1 <> s0) y1 `u` subst (s1 <> s0) y2
                            return (s2 <> s1 <> s0)
                    else do throwError (CannotUnify t1 t2)
u t1@(TSum (FVar p1) n1 x1 y1) t2@(TSum p2 n2 x2 y2)
                  = if n1 == n2
                    then do let s0 = singleton (p1, p2)
                            s1 <- subst s0 x1 `u` subst s0 x2;
                            s2 <- subst (s1 <> s0) y1 `u` subst (s1 <> s0) y2
                            return (s2 <> s1 <> s0)
                    else do throwError (CannotUnify t1 t2)
u t1@(TUnit (FVar p1) n1) t2@(TUnit p2 n2)
                  = if n1 == n2
                    then do return $ singleton (p1, p2)
                    else do throwError (CannotUnify t1 t2)
u t1 t2@(TVar n)
  | n `occurs` t1 && t1 /= t2 = throwError (OccursCheck n t1)
  | otherwise     = return $ singleton (n, t1)
u t1@(TVar n) t2
  | n `occurs` t2 && t1 /= t2 = throwError (OccursCheck n t2)
  | otherwise     = return $ singleton (n, t2)
u t1 t2           = throwError (CannotUnify t1 t2)

-- |Occurs check for Robinson's unification algorithm.
occurs :: TVar -> Type -> Bool
occurs n t = n `elem` (ftv t)

preserveTypeSystem :: Bool
preserveTypeSystem = True

unifyScale :: Scale -> Scale -> Analysis Env
unifyScale s1 s2 =
  case (s1, s2) of
    (SVar v1, SVar v2) -> return $ singleton (v1, s2)
    (SVar v1,       _) -> return $ singleton (v1, s2)
    (_      , SVar v2) -> return $ singleton (v2, s1)
    (_      ,       _) ->
      if s1 == s2
         then return $ mempty
              -- Should be made a warning if we don't want the analysis to
              -- reject programs that are valid according to the underlying
              -- type system.
         else if preserveTypeSystem
                 then return $ mempty
                 else throwError $ MeasureError $ "incompatible scales used: " ++ show s1 ++ " vs. " ++ show s2


unifyBase :: Base -> Base -> Analysis Env
unifyBase b1 b2 =
  case (b1, b2) of
    (BVar v1, BVar v2) -> return $ singleton (v1, b2)
    (BVar v1,       _) -> return $ singleton (v1, b2)
    (_      , BVar v2) -> return $ singleton (v2, b1)
    (_      ,       _) ->
      if b1 == b2
         then return $ mempty
              -- Should be made a warning if we don't want the analysis to
              -- reject programs that are valid in the underlying
              -- type system.
         else if preserveTypeSystem
                 then return $ mempty
                 else throwError $ MeasureError $ "incompatible bases used: " ++ show b1 ++ " vs. " ++ show b2

-- * Singleton Constructors

instance Singleton Env (TVar, Type) where
  singleton (k, a) = Env (M.singleton k a) emptyExtendedEnv

instance Singleton Env (FVar, Flow) where
  singleton (k, a) = Env M.empty $ emptyExtendedEnv { flowMap = M.singleton k a }

instance Singleton Env (SVar, Scale) where
  singleton (k, a) = Env M.empty $ emptyExtendedEnv { scaleMap = M.singleton k a }

instance Singleton Env (BVar, Base) where
  singleton (k, a) = Env M.empty $ emptyExtendedEnv { baseMap = M.singleton k a }
