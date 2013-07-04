{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module FUN.CFA where

import FUN.Base
import FUN.Parsing ( )
import FUN.Labeling

import Text.Printf (printf)

import Prelude hiding (mapM)

import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.List as L (union)

-- import Data.Monoid hiding ((<>), mempty, mconcat Sum (..) )
import Data.Traversable (forM,mapM)

import Control.Monad (join, foldM)
import Control.Applicative hiding (empty)

import Control.Monad.Error (Error (..),ErrorT,runErrorT,throwError)
import Control.Monad.Supply (Supply, SupplyT, supply, evalSupply, evalSupplyT)
import Control.Monad.Trans (lift)

import Data.Set ( Set, empty, union )
import qualified Data.Set as Set


prelude :: CFA (Env, [Decl])
prelude = if False then return (mempty, []) else
  let id = Abs noLabel "x" (Var "x")
      
      predefs =
        [ ("asKelvin",  id, \v -> TArr v (TInt SUnit BNone) (TInt SKelvin BNone)     )
        , ("asCelcius", id, \v -> TArr v (TInt SUnit BNone) (TInt SKelvin BFreezing) )
        , ("asFeet",    id, \v -> TArr v (TInt SUnit BNone) (TInt SFeet BNone)       )        
        , ("asMeters",  id, \v -> TArr v (TInt SUnit BNone) (TInt SMeter BNone)      )        
        , ("asDollars", id, \v -> TArr v (TInt SUnit BNone) (TInt SDollar BNone)     )        
        , ("asEuros",   id, \v -> TArr v (TInt SUnit BNone) (TInt SEuro BNone)       )
        , ("asSeconds", id, \v -> TArr v (TInt SUnit BNone) (TInt SSeconds BNone)    )
        ]
  in do ps <- mapM (\(nm, e, f) -> do v <- fresh; return ( (nm, f v), Decl nm e)) $ predefs
        let (env, ds) = unzip ps
        
        return ( (M.fromList env, emptyExtendedEnv), ds ) 

-- * Type definitions

type TVar = Name -- Type Variable
type FVar = Name -- Flow Variable

data Flow 
  = FVar FVar 
    deriving (Eq, Ord, Show)
      
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
          showScaleBase = if s == SUnit
                             then "" else
                          if b == BNone
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

printFlow :: Map FVar (String, Set Label) -> String
printFlow m = 
  let prefix = "{\n"
      printCon (nm, v) = nm ++ "\t{ " ++ (foldr1 (\x xs -> x ++ ", " ++ xs) . S.toList $ v) ++ " }"
      content = M.foldWithKey (\k a as -> "  " ++ k ++ "\t~> " ++ printCon a ++ "\n" ++ as) "" m
      suffix = "}"
  in prefix ++ content ++ suffix
    
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
refreshAll :: Either TypeError (Env, Prog, Set Constraint) -> Either TypeError (Env, Prog, Set Constraint)
refreshAll env = do (env, p, c) <- env;
                    m <- mapM (withFreshVars . refresh) $ fst env
                    return ((m, snd env), p, c) 

-- |Replaces every type variable with a fresh one.
refresh :: Type -> CFA Type
refresh t1 = do subs <- forM (ftv t1) $ \a ->
                          do b <- fresh :: CFA Type
                             return $ singleton (a, b)
                return $ subst (mconcat subs) t1

-- |Returns the set of free type variables in a type.
ftv :: Type -> [TVar]
ftv TBool           = [ ]
ftv (TInt _ _)      = [ ]
ftv (TVar  n)       = [n]
ftv (TArr  _   a b) = L.union (ftv a) (ftv b)
ftv (TProd _ _ a b) = L.union (ftv a) (ftv b)
ftv (TSum  _ _ a b) = L.union (ftv a) (ftv b)
ftv (TUnit _ _)     = [ ]

emptyExtendedEnv = ExtendedEnv { 
  cfaMap = M.empty, 
  scaleMap = M.empty,
  baseMap = M.empty
}

class Singleton w k where
  singleton :: k -> w

instance Singleton (Map k a) (k, a) where
  singleton = uncurry M.singleton
  
instance Singleton (Set k) k where
  singleton = S.singleton

instance Singleton Env (TVar, Type) where
  singleton (k, a) = (M.singleton k a, emptyExtendedEnv)

  
instance Singleton Env (FVar, Flow) where
  singleton (k, a) = (M.empty, emptyExtendedEnv { cfaMap = M.singleton k a })

instance Singleton Env (SVar, Scale) where
  singleton (k, a) = (M.empty, emptyExtendedEnv { scaleMap = M.singleton k a })

instance Singleton Env (BVar, Base) where
  singleton (k, a) = (M.empty, emptyExtendedEnv { baseMap = M.singleton k a })



class Subst w where
  subst :: Env -> w -> w
 
-- |Substitutes a type for a type variable in a type.
instance Subst Type where
  subst m TBool = TBool
  subst m r@(TInt s b)     = TInt (subst m s) (subst m b)
  subst m v@(TVar n)       = M.findWithDefault v n (fst m)
  subst m (TArr  v    a b) = TArr (subst m v) (subst m a) (subst m b)
  subst m (TProd v nm a b) = TProd (subst m v) nm (subst m a) (subst m b)
  subst m (TSum  v nm a b) = TSum  (subst m v) nm (subst m a) (subst m b)
  subst m (TUnit v nm)     = TUnit (subst m v) nm
  
instance Subst Flow where
  subst m v@(FVar n) = M.findWithDefault v n (cfaMap $ snd m)
  
instance Subst Scale where
  subst m v@(SVar n) = M.findWithDefault v n (scaleMap $ snd m)
  subst m (STimes a b) = STimes (subst m a) (subst m b) 
  subst m (SInverse a) = SInverse (subst m a)
  subst m v@_ = v
  
instance Subst Base where
  subst m v@(BVar n) = M.findWithDefault v n (baseMap $ snd m)
  subst m v@_ = v
  
instance Subst Env where
  subst m (r, w) = (fmap (subst m) r, w)  
  
instance Subst ScaleConstraint where
  subst m (ScaleEquality ss) = ScaleEquality $ map (subst m) ss

instance Subst BaseConstraint where
  subst m (BaseEquality ss) = BaseEquality $ map (subst m) ss
  subst m (BasePreservation (x, y) z) = BasePreservation (subst m x, subst m y) (subst m z)
  subst m (BaseSelection (x, y) z) = BaseSelection (subst m x, subst m y) (subst m z)
  
instance Subst (Set Constraint) where
  subst m = S.map mapper where
    mapper (FlowConstraint nm v r) = FlowConstraint nm (subst m v) r
    mapper (ScaleConstraint ss)    = ScaleConstraint $ subst m ss
    mapper (BaseConstraint ss)     = BaseConstraint $ subst m ss
    
class Fresh t where
  fresh :: CFA t

instance Fresh Type where
  fresh = fmap TVar $ lift (lift supply)
  
instance Fresh Flow where
  fresh = fmap FVar $ lift supply

instance Fresh Scale where
  fresh = fmap SVar $ lift supply
  
instance Fresh Base where
  fresh = fmap BVar $ lift supply


  

-- |Representation for possible errors in algorithm W.
data TypeError
  = CannotDestruct  Type      -- ^ thrown when attempting to destruct a non-product
  | PatternError    TVar TVar -- ^ thrown when pattern matching on a different type
  | UnboundVariable TVar      -- ^ thrown when unknown variable is encountered
  | OccursCheck     TVar Type -- ^ thrown when occurs check in unify fails
  | CannotUnify     Type Type -- ^ thrown when types cannot be unified
  | OtherError      String    -- ^ stores miscellaneous errors
  | NoMsg                     -- ^ please don't be a jackass; don't use this
  | MeasureError    String 
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
  show (MeasureError     s) = "Unit of Measure Error: " ++ s


-- |Occurs check for Robinson's unification algorithm.
occurs :: TVar -> Type -> Bool
occurs n t = n `elem` (ftv t)

data ExtendedEnv = ExtendedEnv { cfaMap :: Map FVar Flow, scaleMap :: Map SVar Scale, baseMap :: Map BVar Base }   

type Env = (Map TVar Type, ExtendedEnv)

type CFA a = ErrorT TypeError (SupplyT FVar (Supply TVar)) a

preserveTypeSystem :: Bool
preserveTypeSystem = True

unifyScale :: Scale -> Scale -> CFA Env
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
                             

unifyBase :: Base -> Base -> CFA Env
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
 

-- |Unification as per Robinson's unification algorithm.
u :: Type -> Type -> CFA Env
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

typeOf :: Lit -> Type
typeOf (Bool    _) = TBool
typeOf (Integer s b _) = TInt s b
 
($*) :: Applicative f => Ord a => Map a b -> a -> f b -> f b
f $* a = \d -> 
  case M.lookup a f of
    Just b  -> pure b
    Nothing -> d

 
(~>) :: TVar -> Type -> Env -> Env
x ~> t = \(m, w) -> (M.insert x t m, w)

(<>) :: Env -> Env -> Env
(<>) m@(s2, a2) (s1, a1) = ( s2 `M.union` (subst m <$> s1)
                           , ExtendedEnv { 
                               cfaMap   = cfaMap   a2 `M.union` (subst m <$> cfaMap   a1),
                               scaleMap = scaleMap a2 `M.union` (subst m <$> scaleMap a1), 
                               baseMap  = baseMap  a2 `M.union` (subst m <$> baseMap  a1)   
                             }
                           )
mempty :: Env
mempty = (M.empty, emptyExtendedEnv)

mconcat :: [Env] -> Env
mconcat = foldr (<>) mempty
 
constraint :: String -> Flow -> Label -> Set Constraint
constraint nm a l = singleton $ FlowConstraint nm a l                               

    
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
                        (t2, s2, c2) <- cfa e . subst s1 $ env
                        
                        a <- fresh;
                        b <- fresh
                        
                        s3 <- subst s2 t1 `u` TArr b t2 a

                        return ( subst s3 a 
                               , s3 <> s2 <> s1
                               , subst (s3 <> s2) c1 `union` 
                                 subst  s3        c2
                               )
  
  Let x e1 e2     -> do (t1, s1, c1) <- cfa e1 $ env;
                        (t2, s2, c2) <- cfa e2 . (x ~> t1) . subst s1 $ env

                        return ( t2
                               , s2 <> s1
                               , subst s2 c1 `union` c2
                               )

                    
  -- * adding if-then-else constructs
                    
  ITE b e1 e2     -> do (t0, s0, c0) <- cfa b $ env;
                        (t1, s1, c1) <- cfa e1 . subst s0 $ env
                        (t2, s2, c2) <- cfa e2 . subst (s1 <> s0) $ env
                        
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
                                      , constraint nm b_0 pi
                                      )
  -- * adding product types
  Con pi nm (Prod x y)   -> do (t1, s1, c1) <- cfa x $ env
                               (t2, s2, c2) <- cfa y . subst s1 $ env
      
                               b_0 <- fresh
      
                               return ( TProd b_0 nm (subst s2 t1) t2
                                      , s2 <> s1
                                      , subst s2 c1 `union` 
                                                 c1 `union` constraint nm b_0 pi 
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

  Des nm e1 (UnUnit e2)     -> do (t1, s1, c1) <- cfa e1 $ env
                                             
                                  b_0 <- fresh
                                             
                                  s2 <- t1 `u` TUnit b_0 nm
                                  
                                  (t3, s3, c3) <- cfa e2 . subst (s2 <> s1) $ env
                                  
                                  return ( t3
                                         , s3 <> s2 <> s1
                                         , subst (s3 <> s2) c1 `union` c3
                                         )

  Des nm e1 (UnProd x y e2)   -> do (t1, s1, c1) <- cfa e1 $ env
                                  
                                    a_x <- fresh
                                    a_y <- fresh
                                    
                                    b_0 <- fresh
                                    
                                    s2 <- t1 `u` TProd b_0 nm a_x a_y
                                    (t3, s3, c3) <- cfa e2 . (y ~> a_y) . (x ~> a_x) . subst (s2 <> s1) $ env

                                    return ( t3
                                           , s3 <> s2 <> s1
                                           , subst (s3 <> s2) c1 `union` c3
                                           )
                                           
  Des nm e1 (UnSum (x, ex) (y, ey))     -> do (t1, s1, c1) <- cfa e1 $ env
                                             
                                              a_x <- fresh
                                              a_y <- fresh
                                              
                                              b_0 <- fresh
                                              
                                              s2 <- t1 `u` TSum b_0 nm a_x a_y
                                             
                                              (tx, s3, c3) <- cfa ex . (x ~> a_x) . subst (s2 <> s1) $ env
                                              (ty, s4, c4) <- cfa ey . (y ~> a_y) . subst (s3 <> s2 <> s1) $ env
                                             
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
                                        
                    (t1, s1, c1) <- cfa x $ env    
                    s2 <- t1 `u` TInt rx bx
                    
                    
                    (t3, s3, c3) <- cfa y . subst (s2 <> s1) $ env
                    s4 <- t3 `u` TInt ry by
                    
                    rz <- fresh
                    bz <- fresh
                    
                    let c0 = case op of
                          Add -> scaleEquality [rx, ry, rz]                  `union` selectBase   (bx, by) bz                                    
                          Sub -> scaleEquality [rx, ry, rz]                  `union` preserveBase (bx, by) bz                                                         
                          Mul -> scaleEquality [rz, (STimes rx ry)]          `union` baseEquality [bx, by, bz, BNone]
                          Div -> scaleEquality [rz, STimes rx (SInverse ry)] `union` baseEquality [bx, by, bz, BNone]      
                                                           

                    return ( TInt rz bz
                           , s4 <> s3 <> s2 <> s1
                           , subst (s4 <> s3 <> s2 <> s1) c0 `union`
                             subst (s4 <> s3 <> s2)       c1 `union` 
                             subst  s4                    c3       
                           )
  
data Constraint 
  = FlowConstraint String Flow Label
  | ScaleConstraint ScaleConstraint
  | BaseConstraint BaseConstraint
  deriving (Eq, Ord, Show)

   
scaleEquality :: [Scale] -> Set Constraint
scaleEquality = S.singleton . ScaleConstraint . ScaleEquality

baseEquality :: [Base] -> Set Constraint
baseEquality = S.singleton . BaseConstraint . BaseEquality 

selectBase :: (Base, Base) -> Base -> Set Constraint
selectBase xy z = S.singleton $ BaseConstraint $ BaseSelection xy z 

preserveBase :: (Base, Base) -> Base -> Set Constraint
preserveBase xy z = S.singleton $ BaseConstraint $ BasePreservation xy z 

solveFlowConstraints :: Set Constraint -> Map FVar (String, Set Label)
solveFlowConstraints = 
  let mergeNames p q = let (np, cp) = span (/= '.') p
                           (nq, cq) = span (/= '.') q
                       in if np == nq
                             then if cp == cq
                                     then p
                                     else np ++ ".{" ++ tail cp ++ ", " ++ tail cq ++ "}"
                             else error $ "different constructors used to construct sum type (\"" ++ np ++ "\" vs. \"" ++ nq ++ "\")"
                    
      extractFlowConstraint (FlowConstraint nm v l) = 
        case v of
          FVar r -> [M.singleton r (nm, S.singleton l)]
      extractFlowConstraint _ = []
  in M.unionsWith (\(nx, vx) (ny, vy) -> (mergeNames nx ny, vx `union` vy) ) . concatMap extractFlowConstraint . S.toList
     
data ScaleConstraint
  = ScaleEquality [Scale]
    deriving (Eq, Ord)
     
instance Show ScaleConstraint where
  show (ScaleEquality ss) = "equal: " ++ (foldr1 (\x xs -> x ++ ", " ++ xs) . fmap show $ ss) 
     
solveScaleConstraints :: Set Constraint -> [ScaleConstraint]
solveScaleConstraints = concatMap findScales . S.toList where
  findScales (ScaleConstraint ss) = [ss]
  findScales _                    = [  ]

data BaseConstraint 
  = BaseEquality [Base] 
  | BasePreservation (Base, Base) Base
  | BaseSelection (Base, Base) Base
    deriving (Eq, Ord)
    
instance Show BaseConstraint where
  show (BaseEquality bs) = "equal: " ++ (foldr1 (\x xs -> x ++ ", " ++ xs) . fmap show $ bs) 
  show (BasePreservation (x, y) z) = "preservation: if " ++ show y ++ " = none then " ++ show x 
                                              ++ "; if " ++ show x ++ " = " ++ show y ++ "then none" 
                                              ++ "; else undefined"
  show (BaseSelection (x, y) z) = "selection: if " ++ show y ++ " = none then " ++ show x
                                        ++ "; if " ++ show x ++ " = none then " ++ show y
                                        ++ "; else error"
    
solveBaseConstraints :: Set Constraint -> [BaseConstraint]
solveBaseConstraints = concatMap findBases . S.toList where
  findBases (BaseConstraint bs) = [bs]
  findBases _                   = [  ]


printFlowInformation :: Map FVar (String, Set Label) -> String
printFlowInformation m = 
  let prefix = "{\n"
      printCon (nm, v) = nm ++ "\t{ " ++ (foldr1 (\x xs -> x ++ ", " ++ xs) . S.toList $ v) ++ " }"
      content = M.foldWithKey (\k a as -> "  " ++ k ++ "\t~> " ++ printCon a ++ "\n" ++ as) "" m
      suffix = "}"
  in prefix ++ content ++ suffix

printScaleInformation :: [ScaleConstraint] -> String
printScaleInformation m =
  let prefix = "{\n"
      content = foldr (\x xs -> "  " ++ show x ++ "\n" ++ xs) "" m
      suffix = "}"
  in prefix ++ content ++ suffix

printBaseInformation :: [BaseConstraint] -> String
printBaseInformation m = 
  let prefix = "{\n"
      content = foldr (\x xs -> "  " ++ show x ++ "\n" ++ xs) "" m
      suffix = "}"
  in prefix ++ content ++ suffix


   
-- * Algorithm W for Type Inference

-- |Runs algorithm W on a list of declarations, making each previous
--  declaration an available expression in the next.      

runCFA :: [Decl] -> Either TypeError (Env, Prog, Set Constraint)
runCFA ds = 
  let addDecl :: (Env, Set Constraint) -> Decl-> CFA (Env, Set Constraint)
      addDecl (env, c0) (Decl x e) = do (t, s1, c1) <- cfa e $ env
                                  
                                        let s2 = (M.empty, snd s1)
                                    
                                        return ( (M.insert x t . fmap (subst s2) $ fst env, snd env)
                                               , subst s1 c0 `union` c1
                                               )                                          

      
  in refreshAll . withFreshVars $ do (env, lib) <- prelude
  
                                     let (labeledLib, labeledDecls) = runLabel $ (lib, ds)
  
                                     (env, c0) <- foldM addDecl (env, empty) $ labeledDecls
                                     return (env, Prog $ labeledLib ++ labeledDecls, c0)
