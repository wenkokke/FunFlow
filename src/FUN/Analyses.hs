-- (C) 2013 Pepijn Kokke & Wout Elsinghorst

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module FUN.Analyses where

import FUN.Base
import FUN.Labeling
import FUN.Analyses.Flow
import FUN.Analyses.Measure
import FUN.Analyses.Utils

import Prelude hiding (mapM)

import Data.Monoid hiding ( Sum )
import Data.Functor ((<$>))

import Control.Monad (foldM)
import Control.Monad.Error 
  ( Error (..)
  , ErrorT
  , runErrorT, throwError
  )
  
import Control.Monad.Supply 
  ( Supply, SupplyT
  , supply, evalSupply, evalSupplyT
  )
  
import Control.Monad.Trans (lift)

import Data.Traversable (forM,mapM)


import Data.Map (Map)
import Data.Set ( Set, empty, union )
import qualified Data.Map  as M
import qualified Data.Set  as S
import qualified Data.List as L

import Text.Printf (printf)

-- |Collection of built-in functions available to all programs. At the time of writing, these
--  all serve to introduce (the by default) unitless integers to the world of typed units of
--  measure. The measure analysis makes sure all measure annotations properly propagate through
--  the program.
prelude :: Analysis (Env, [Decl])
prelude = 
  let id = Abs noLabel "x" (Var "x")
      predefs =
        [ ("asKelvin",  "Kelvin", id, \v s -> TArr v (TInt SNil BNil) (TInt s  BNil))
        , ("asCelcius", "Kelvin", id, \v s -> TArr v (TInt SNil BNil) (TInt s  (BCon "Freezing")))
        , ("asFeet",    "Feet",   id, \v s -> TArr v (TInt SNil BNil) (TInt s  BNil))
        , ("asMeters",  "Meter",  id, \v s -> TArr v (TInt SNil BNil) (TInt s  BNil))
        , ("asDollars", "Dollar", id, \v s -> TArr v (TInt SNil BNil) (TInt s  BNil))
        , ("asEuros",   "Euro",   id, \v s -> TArr v (TInt SNil BNil) (TInt s  BNil))
        , ("asSeconds", "Second", id, \v s -> TArr v (TInt SNil BNil) (TInt s  BNil))
        ]
  in do ps <- mapM (\(nm, u, e, f) -> do v <- fresh;
                                        
                                         return ( (nm, f v $ SCon u), Decl nm e) ) $ predefs;
        let (env, ds) = unzip ps;
        return ( mempty { typeMap = TSubst $ M.fromList env }
               , ds
               )
        
data PrintAnnotations 
  = TypeAnnotations
  | FlowAnnotations
  | ScaleAnnotations
  | BaseAnnotations
        
printProgram :: Bool -> Program -> Env -> String
printProgram annotations (Prog p) env = 
  let funcType (Decl nm e) = case M.lookup nm (getTSubst $ typeMap env) of
                               Just r  -> nm ++ " :: " ++ (showType annotations r)
                               Nothing -> error $ "printProgram: no matching type found for function \"" ++ nm ++ "\""
      funcBody = showDecl annotations
      prefix = "{\n"
      suffix = "}"
      
      printer x xs = "  " ++ funcType x ++ "\n  " ++ funcBody x ++ "\n\n" ++ xs 
      
  in prefix ++ foldr printer "" p ++ suffix
        
        
-- * Type definitions

-- |Type variables
type TVar = String

-- |Representation for inferred types in our functional language. The Flow field
--  holds flow variables to which Control Flow Constraints are attached during the
--  execution of W. 
data Type
  = TVar  TVar
  | TBool
  | TInt  Scale Base
  | TArr  Flow Type Type        -- Function Arrow
  | TProd Flow Name Type Type   -- 
  | TSum  Flow Name Type Type
  | TUnit Flow Name
  deriving (Eq, Ord)

instance Show Type where
  show = showType False

-- |Pretty print a given type. The boolean parameter tells weither to print type 
--  annotations (when True) or not (when False). 
showType :: Bool -> Type -> String
showType cp =
  let printAnn (FVar s) = if cp then "{" ++ s ++ "}" else ""
      printAnn (FSet l) = "{" ++ (L.foldr1 (\x xs -> x ++ ", " ++ xs) . map showLabel . S.toList $ l) ++ "}" where
         showLabel l = "[" ++ l ++ "]"
      showType ty = case ty of
        TBool -> "Bool"
        TInt s b -> "Integer" ++ showScaleBase where
          showScaleBase = if s == SNil
                             then "" else
                          if b == BNil
                             then "{" ++ show s ++ "}"
                             else "{" ++ show s ++ "@" ++ show b ++ "}"
        TVar n -> n
        TArr  v a b -> printf "%s -%s> %s" (wrap a) (printAnn v) (wrap b) where
            wrap ty@(TArr _ _ _) = printf "(%s)" (showType ty)
            wrap ty              = showType ty
        TProd v nm a b -> printf "%s%s(%s, %s)" nm (printAnn v) (wrap a) (wrap b) where
            wrap ty@(TProd _ _ _ _) = printf "(%s)" (showType ty)
            wrap ty@(TSum  _ _ _ _) = printf "(%s)" (showType ty)
            wrap ty@(TArr _ _ _)    = printf "(%s)" (showType ty)
            wrap ty                 = showType ty
        TSum v nm a b -> printf "%s%s %s %s" nm (printAnn v) (wrap a) (wrap b) where
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

-- |Extract the type from primitive literals
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

-- |The Analysis monad, the main datatype used by our implementation of W. The various
--  monads have the following purposes:
--
--  ErrorT: this transformer is used for error reporting
--  SupplyT: this transformer threads a supply of fresh annotation variables. The supply
--           is shared by the various analyses.
--  Supply: thread a supply of fresh type variables
type Analysis a = ErrorT TypeError (SupplyT FVar (Supply TVar)) a


-- |`(x ~> t) env` can be read as 'simplify variable `x` to type `t` in the environment `env`
(~>) :: TVar -> Type -> Env -> Env
x ~> t = \env -> env { typeMap = TSubst $ M.insert x t . getTSubst . typeMap $ env }


-- * Algorithm W for Type Inference

instance Rewrite Constraint where
  simplify (ScaleConstraint ss) = ScaleConstraint $ simplify ss
  simplify v@_ = v
     
-- |Runs Algorithm W on a list of declarations, making each previous
--  declaration an available expression in the next.
analyseProgram :: Program -> Either TypeError (Env, Program, Set Constraint)
analyseProgram (Prog ds) =
  let analyseDecl :: (Env, Set Constraint) -> Decl-> Analysis (Env, Set Constraint)
      analyseDecl (env, c0) (Decl x e) = do (t, s1, c1) <- analyse e $ env

                                            let s2 = s1 { typeMap = mempty }

                                            return ( env { 
                                                       typeMap = TSubst $ M.insert x t . fmap (subst s2) $ getTSubst . typeMap $ env 
                                                     } 
                                                   , subst s1 c0 `union` c1
                                                   )

  in refreshAll . withFreshVars $ do (env, lib) <- prelude

                                     let (labeledLib, labeledDecls) = runLabel $ (lib, ds)

                                     (env, c0) <- foldM analyseDecl (env, empty) $ labeledDecls
                                     
                                     let (f_s1, f_c1) = solveConstraints . extractFlowConstraints $ c0
                                         c1 = S.map FlowConstraint f_c1                                        
                                         
                                         (s_s2, s_c2) = solveConstraints . extractScaleConstraints $ c0
                                         c2 = S.map ScaleConstraint s_c2     
                                     
                                         (b_s3, b_c3) = solveConstraints . extractBaseConstraints  $ c0
                                         c3 = S.map BaseConstraint b_c3
                                     
                                     return ( subst b_s3 . subst s_s2 . subst f_s1 $ env 
                                            , Prog $ labeledLib ++ labeledDecls
                                            , simplify $ c1 `union` c2 `union` c3
                                            )

-- |Runs the Algorithm W inference for Types and generates constraints later used 
--  by Control Flow analysis and Measure Analysis.
analyse :: Expr -> Env -> Analysis (Type, Env, Set Constraint)
analyse exp env = case exp of
  Lit l           -> return ( typeOf l
                            , mempty
                            , empty
                            )

  Var x           -> do v <- (getTSubst (typeMap env) $* x) $ throwError (UnboundVariable x)

                        return ( v
                               , mempty
                               , empty
                               )

  Abs pi x e      -> do a_x <- fresh
                        b_0 <- fresh

                        (t0, s0, c0) <- analyse e . (x ~> a_x) $ env

                        return ( TArr b_0 (subst s0 a_x) t0
                               , s0
                               , c0 `union` flowConstraint b_0 pi
                               )

  -- * adding fixpoint operators

  Fix pi f x e    -> do a_x <- fresh
                        a_0 <- fresh
                        b_0 <- fresh

                        (t0, s0, c0) <- analyse e . (f ~> TArr b_0 a_x a_0) . (x ~> a_x) $ env

                        (    s1, c1) <- t0 `u` subst s0 a_0

                        let b_1 = subst (s1 <> s0) b_0

                        return ( TArr b_1 (subst (s1 <> s0) a_x) (subst s1 t0)
                               , s1 <> s0
                               , subst s1 c0 `union` 
                                          c1 `union` flowConstraint b_1 pi
                               )


  App f e         -> do (t1, s1, c1) <- analyse f $ env
                        (t2, s2, c2) <- analyse e . subst s1 $ env

                        a <- fresh;
                        b <- fresh

                        (    s3, c3) <- subst s2 t1 `u` TArr b t2 a

                        return ( subst s3 a
                               , s3 <> s2 <> s1
                               , subst (s3 <> s2) c1 `union`
                                 subst  s3        c2 `union`
                                                  c3
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

                        (    s3, c3) <- subst (s2 <> s1) t0 `u` TBool
                        (    s4, c4) <- subst s3 t2 `u` subst (s3 <> s2) t1;

                        return ( subst (s4 <> s3) t2
                               , s4 <> s3 <> s2 <> s1
                               , subst (s4 <> s3 <> s2 <> s1) c0 `union`
                                 subst (s4 <> s3 <> s2)       c1 `union`
                                 subst (s4 <> s3)             c2 `union`
                                 subst  s4                    c3 `union`
                                                              c4
                               )

  Con pi nm Unit         -> do b_0 <- fresh

                               return ( TUnit b_0 nm
                                      , mempty
                                      , flowConstraint b_0 pi
                                      )
  -- * Product types
  
  Con pi nm (Prod x y)   -> do (t1, s1, c1) <- analyse x $ env
                               (t2, s2, c2) <- analyse y . subst s1 $ env

                               b_0 <- fresh

                               return ( TProd b_0 nm (subst s2 t1) t2
                                      , s2 <> s1
                                      , subst s2 c1 `union`
                                                 c2 `union` flowConstraint b_0 pi
                                      )
  -- * Sum types
  
  Con pi nm (Sum L t)   -> do (t1, s1, c1) <- analyse t $ env
                              t2 <- fresh

                              b_0 <- fresh

                              return ( TSum b_0 nm t1 t2
                                      , s1
                                      , c1 `union` flowConstraint b_0 pi
                                      )
  Con pi nm (Sum R t)   -> do (t2, s1, c1) <- analyse t $ env
                              t1 <- fresh

                              b_0 <- fresh

                              return ( TSum b_0 nm t1 t2
                                      , s1
                                      , c1 `union` flowConstraint b_0 pi
                                      )

  -- * Destructing types
                                      
                                      
  Des nm e1 (UnUnit e2)     -> do (t1, s1, c1) <- analyse e1 $ env

                                  b_0 <- fresh

                                  (    s2, c2) <- t1 `u` TUnit b_0 nm

                                  (t3, s3, c3) <- analyse e2 . subst (s2 <> s1) $ env

                                  return ( t3
                                         , s3 <> s2 <> s1
                                         , subst (s3 <> s2) c1 `union`
                                           subst  s3        c2 `union` 
                                                            c3
                                         )

  Des nm e1 (UnProd x y e2)   -> do (t1, s1, c1) <- analyse e1 $ env

                                    a_x <- fresh
                                    a_y <- fresh

                                    b_0 <- fresh

                                    (    s2, c2) <- t1 `u` TProd b_0 nm a_x a_y
                                    (t3, s3, c3) <- analyse e2 . (y ~> a_y) . (x ~> a_x) . subst (s2 <> s1) $ env

                                    return ( t3
                                           , s3 <> s2 <> s1
                                           , subst (s3 <> s2) c1 `union`
                                             subst  s3        c2 `union`
                                                              c3
                                           )

  Des nm e1 (UnSum (x, ex) (y, ey))     -> do (t1, s1, c1) <- analyse e1 $ env

                                              a_x <- fresh
                                              a_y <- fresh

                                              b_0 <- fresh

                                              (    s2, c2) <- t1 `u` TSum b_0 nm a_x a_y

                                              (tx, s3, c3) <- analyse ex . (x ~> a_x) . subst (s2 <> s1) $ env
                                              (ty, s4, c4) <- analyse ey . (y ~> a_y) . subst (s3 <> s2 <> s1) $ env

                                              (    s5, c5) <- tx `u` ty

                                              return ( subst s5 tx
                                                     , s5 <> s4 <> s3 <> s2 <> s1
                                                     , subst (s5 <> s4 <> s3 <> s2) c1 `union`
                                                       subst (s5 <> s4 <> s3)       c2 `union`
                                                       subst (s5 <> s4)             c3 `union`
                                                       subst  s5                    c4 `union`
                                                                                    c5
                                                     )

                                                     
  -- * Binary operators
                                                     
  Oper op x y -> do rx <- fresh
                    bx <- fresh

                    ry <- fresh
                    by <- fresh

                    (t1, s1, c1) <- analyse x $ env
                    (    s2, c2) <- t1 `u` TInt rx bx


                    (t3, s3, c3) <- analyse y . subst (s2 <> s1) $ env
                    (    s4, c4) <- t3 `u` TInt ry by

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
                             subst (s4 <> s3)             c2 `union`
                             subst  s4                    c3 `union`
                                                          c4
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
refreshAll :: Either TypeError (Env, Program, Set Constraint) -> Either TypeError (Env, Program, Set Constraint)
refreshAll env = do (env, p, c) <- env;
                    m <- mapM (withFreshVars . refresh) $ getTSubst . typeMap $ env
                    return ( env { 
                               typeMap = TSubst m 
                             }
                           , p
                           , c
                           )

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

flowEquality :: Flow -> Flow -> Set Constraint
flowEquality a b = singleton $ FlowConstraint $ FlowEquality a b
    
-- |Construct a Scale resp. Base Equality Constraint from a list of Scale resp. Base annotations. All 
--  annotations in the list will be unified post-W
scaleEquality :: [Scale] -> Set Constraint
scaleEquality = S.singleton . ScaleConstraint . ScaleEquality . S.fromList

-- |Construct a Base Equality Constraint from a list of Bases all deemed equal.
baseEquality :: [Base] -> Set Constraint
baseEquality = S.singleton . BaseConstraint . BaseEquality . S.fromList

-- |Constraint generated by the addition of two measures
selectBase :: (Base, Base) -> Base -> Set Constraint
selectBase xy z = S.singleton $ BaseConstraint $ BaseSelection xy z

-- |Constraint generated by the subtraction of two measures
preserveBase :: (Base, Base) -> Base -> Set Constraint
preserveBase xy z = S.singleton $ BaseConstraint $ BasePreservation xy z

-- |Constraint generated by the construction of a program point 
flowConstraint :: Flow -> Label -> Set Constraint
flowConstraint f l = singleton $ FlowConstraint $ FlowEquality f (FSet $ S.singleton l)

-- |Seperate the Flow Constraints from the rest of the Constraint set
extractFlowConstraints :: Set Constraint -> Set FlowConstraint
extractFlowConstraints = unionMap findFlows where
  findFlows (FlowConstraint r)      = S.singleton r
  findFlows _                       = S.empty

-- |Seperate the Scale Constraints from the rest of the Constraint set
extractScaleConstraints :: Set Constraint -> Set ScaleConstraint
extractScaleConstraints = unionMap findScales where
    findScales (ScaleConstraint ss) = S.singleton ss
    findScales _                    = S.empty

-- |Seperate the Base Constraints from the rest of the Constraint set
extractBaseConstraints :: Set Constraint -> Set BaseConstraint
extractBaseConstraints = unionMap findBases where
  findBases (BaseConstraint bs) = S.singleton bs
  findBases _                   = S.empty
                    
-- * Environments

newtype TSubst = TSubst { 
    getTSubst :: Map TVar Type
  } deriving (Eq, Ord, Show)

instance Subst TSubst TSubst where
  subst m (TSubst r) = TSubst $ M.map (subst m) r
  
instance Subst FSubst Type where 
  subst m TBool            = TBool
  subst m (TInt s b)       = TInt  s b
  subst m (TArr  f    a b) = flip3 TArr (subst m a) (subst m b) $ 
    case f of 
      FVar n -> M.findWithDefault f n $ getFSubst m
      _      -> f
  subst m (TProd f nm a b) = flip4 TProd nm (subst m a) (subst m b) $ 
    case f of 
      FVar n -> M.findWithDefault f n $ getFSubst m
      _      -> f
  subst m (TSum  f nm a b) = flip4 TSum  nm (subst m a) (subst m b) $ 
    case f of 
      FVar n -> M.findWithDefault f n $ getFSubst m
      _      -> f
  subst m (TUnit f nm)     = flip2 TUnit nm $ 
    case f of 
      FVar n -> M.findWithDefault f n $ getFSubst m
      _      -> f
  subst m v@(TVar _)       = v

  
-- |Substitutes a type for a type variable in a type.
instance Subst SSubst Type where
  subst m TBool               = TBool
  subst m (TInt s b)          = flip TInt b $ case s of
                                     SVar n   -> M.findWithDefault s n $ getSSubst m
                                     SInv s   -> SInv (subst m s)
                                     SMul x y -> SMul (subst m x) (subst m y)
                                     _        -> s
  subst m (TArr  v    a b)    = TArr  v (subst m a) (subst m b)
  subst m (TProd v nm a b)    = TProd v nm (subst m a) (subst m b)
  subst m (TSum  v nm a b)    = TSum  v nm (subst m a) (subst m b)
  subst m (TUnit v nm)        = TUnit v nm
  subst m v@(TVar _)          = v

instance Subst BSubst Type where
  subst m TBool               = TBool
  subst m (TInt s b)          = TInt  s $ case b of
                                               BVar n -> M.findWithDefault b n $ getBSubst m
                                               _      -> b
  subst m (TArr  v    a b)    = TArr  v (subst m a) (subst m b)
  subst m (TProd v nm a b)    = TProd v nm (subst m a) (subst m b)
  subst m (TSum  v nm a b)    = TSum  v nm (subst m a) (subst m b)
  subst m (TUnit v nm)        = TUnit v nm
  subst m v@(TVar _)          = v

  
  
instance Subst FSubst TSubst where
  subst m (TSubst r) = TSubst $ M.map (subst m) r
  
instance Subst SSubst TSubst where
  subst m (TSubst r) = TSubst $ M.map (subst m) r

instance Subst BSubst TSubst where
  subst m (TSubst r) = TSubst $ M.map (subst m) r
  
instance Monoid TSubst where
  s `mappend` t = TSubst $ getTSubst s `M.union` getTSubst (subst s t)
  mempty        = TSubst $ M.empty
  
data Env = Env { 
    typeMap  :: TSubst          -- ^ Type substitutions used in W
  , flowMap  :: FSubst
  , scaleMap :: SSubst
  , baseMap  :: BSubst
  }

instance Subst TSubst Type where
  subst m f@(TVar n) = M.findWithDefault f n (getTSubst m)
  subst m r@ TBool     = r
  subst m r@(TInt _ _) = r
  
  subst m (TArr  f    a b) = TArr  f    (subst m a) (subst m b)
  subst m (TProd f nm a b) = TProd f nm (subst m a) (subst m b)
  subst m (TSum  f nm a b) = TSum  f nm (subst m a) (subst m b)
  subst m (TUnit f nm)     = TUnit f nm

-- |Substitutes a type for a type variable in a type.
instance Subst Env Type where
  subst m TBool = TBool
  subst m r@(TInt s b)     = TInt  (subst (scaleMap m) s) (subst (baseMap m) b)
  subst m f@(TVar _)       = subst (typeMap m) f
  
  subst m (TArr  f    a b) = TArr  (subst (flowMap m) f)    (subst m a) (subst m b)
  subst m (TProd f nm a b) = TProd (subst (flowMap m) f) nm (subst m a) (subst m b)
  subst m (TSum  f nm a b) = TSum  (subst (flowMap m) f) nm (subst m a) (subst m b)
  subst m (TUnit f nm)     = TUnit (subst (flowMap m) f) nm

instance Subst Env Env where
  subst m env = env { typeMap = TSubst . fmap (subst m) . getTSubst . typeMap $ env }

instance Subst Env Constraint where
  subst m (FlowConstraint r)   = FlowConstraint $ subst m r
  subst m (ScaleConstraint ss) = ScaleConstraint $ subst m ss
  subst m (BaseConstraint ss)  = BaseConstraint $ subst m ss
  
instance Subst Env Flow where
  subst e = subst (flowMap e)

instance Subst Env Scale where
  subst e = subst (scaleMap e)

instance Subst Env Base where
  subst e = subst (baseMap e)

instance Subst FSubst Env where
  subst s env = env { typeMap = subst s (typeMap env), flowMap = s <> flowMap env }
  
instance Subst SSubst Env where
  subst s env = env { typeMap = subst s (typeMap env), scaleMap = s <> scaleMap env }

instance Subst BSubst Env where
  subst s env = env { typeMap = subst s (typeMap env), baseMap = s <> baseMap env }

instance Monoid Env where                    
  -- |Substitutions can be chained by first recursively substituting the left substitution
  --  over the right environment then unioning with the left invironment
  p `mappend` q = Env { 
    typeMap = typeMap p <> typeMap q,
    flowMap = flowMap p <> flowMap q,
    scaleMap = scaleMap p <> scaleMap q,
    baseMap = baseMap p <> baseMap q
  }
      
  mempty = Env { typeMap = mempty, flowMap = mempty, scaleMap = mempty, baseMap = mempty }

  
instance Subst FSubst Constraint where
  subst s (FlowConstraint c) = FlowConstraint $ subst s c
  subst s v                  = v
  
instance Subst SSubst Constraint where
  subst s (ScaleConstraint c) = ScaleConstraint $ subst s c
  subst s v                   = v
  
instance Subst BSubst Constraint where
  subst s (BaseConstraint c) = BaseConstraint $ subst s c
  subst s v                  = v
 

-- * Unifications

-- |Unification as per Robinson's unification algorithm.

u :: Type -> Type -> Analysis (Env, Set Constraint)
u TBool TBool = return $ mempty
u (TInt r1 b1) (TInt r2 b2) = return (mempty, scaleEquality [r1, r2] `union` baseEquality [b1, b2])
u (TArr p1 a1 b1) (TArr p2 a2 b2)
                  = do let c0 = flowEquality p1 p2
                       (s1, c1) <- a1 `u` a2
                       (s2, c2) <- subst s1 b1 `u` subst s1 b2
                       return (s2 <> s1, c0 `union` c1 `union` c2)
u t1@(TProd p1 n1 x1 y1) t2@(TProd p2 n2 x2 y2)
                  = if n1 == n2
                    then do let c0 = flowEquality p1 p2
                            (s1, c1) <- x1 `u` x2;
                            (s2, c2) <- subst s1 y1 `u` subst s1 y2
                            return (s2 <> s1, c0 `union` c1 `union` c2)
                    else do throwError (CannotUnify t1 t2)
u t1@(TSum p1 n1 x1 y1) t2@(TSum p2 n2 x2 y2)
                  = if n1 == n2
                    then do let c0 = flowEquality p1 p2
                            (s1, c1) <- x1 `u` x2;
                            (s2, c2) <- subst s1 y1 `u` subst s1 y2
                            return (s2 <> s1, c0 `union` c1 `union` c2)
                    else do throwError (CannotUnify t1 t2)
u t1@(TUnit p1 n1) t2@(TUnit p2 n2)
                  = if n1 == n2
                    then do let c0 = flowEquality p1 p2
                            return $ (mempty, c0)
                    else do throwError (CannotUnify t1 t2)
u t1 t2@(TVar n)
  | n `occurs` t1 && t1 /= t2 = throwError (OccursCheck n t1)
  | otherwise     = return $ (singleton (n, t1), empty)
u t1@(TVar n) t2
  | n `occurs` t2 && t1 /= t2 = throwError (OccursCheck n t2)
  | otherwise     = return $ (singleton (n, t2), empty)
u t1 t2           = throwError (CannotUnify t1 t2)

-- |Occurs check for Robinson's unification algorithm.
occurs :: TVar -> Type -> Bool
occurs n t = n `elem` (ftv t)   
 
-- * Singleton Constructors

instance Singleton Env (TVar, Type) where
  singleton (k, a) = mempty { typeMap = TSubst $ M.singleton k a } 

instance Singleton Env (FVar, Flow) where
  singleton (k, a) = mempty { flowMap = FSubst $ M.singleton k a }

instance Singleton Env (SVar, Scale) where
  singleton (k, a) = mempty { scaleMap = SSubst $ M.singleton k a }

instance Singleton Env (BVar, Base) where
  singleton (k, a) = mempty { baseMap = BSubst $ M.singleton k a }
