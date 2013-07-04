{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module FUN.Analyses.Measure where

import FUN.Analyses.Utils

import Data.Monoid
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

type SVar = String
type SCon = String
type BVar = String
type BCon = String

data Scale
  = SVar SVar
  | SCon SCon
  | SNil
  | SMul Scale Scale
  | SInv Scale
  deriving (Eq, Ord)

data Base
  = BVar BVar
  | BCon BCon
  | BNil
  deriving (Eq, Ord)

instance Show Scale where
  show SNil               = "Unit"
  show (SVar v)           = "[" ++ v ++ "]"
  show (SCon c)           = c
  show (SMul a (SInv b))  = "(" ++ show a ++ "/" ++ show b ++ ")"
  show (SMul a b)         = "(" ++ show a ++ "*" ++ show b ++ ")"
  show (SInv a)           = "1/(" ++ show a ++ ")"

instance Show Base where
  show BNil     = "None"
  show (BVar v) = "[" ++ v ++ "]"
  show (BCon c) = c

-- * Constraints
  
data ScaleConstraint
  = ScaleEquality (Set Scale)
  deriving (Eq, Ord)
     
instance Show ScaleConstraint where
  show (ScaleEquality ss) = "equal: " ++ (foldr1 (\x xs -> x ++ ", " ++ xs) . map show . S.toList $ ss)
  
data BaseConstraint 
  = BaseEquality (Set Base)
  | BasePreservation (Base, Base) Base
  | BaseSelection (Base, Base) Base
  deriving (Eq, Ord)
    
instance Show BaseConstraint where
  show (BaseEquality bs)
    = "equal: " ++ (foldr1 (\x xs -> x ++ ", " ++ xs) . map show . S.toList $ bs) 
  show (BasePreservation (x, y) z)
    = "preservation: if " ++ show y ++ " = none then " ++ show x 
                          ++ "; if " ++ show x ++ " = " ++ show y ++ "then none" 
                          ++ "; else undefined"
  show (BaseSelection (x, y) z)
    = "selection: if " ++ show y ++ " = none then " ++ show x
                       ++ "; if " ++ show x ++ " = none then " ++ show y
                       ++ "; else error"

-- * Constraint Solving

solveScaleConstraints :: Set ScaleConstraint -> SSubst
solveScaleConstraints = S.foldr (<>) mempty . S.map solveScaleConstraint where
  solveScaleConstraint (ScaleEquality cs) = solveVars cs

solveVars :: Set Scale -> SSubst
solveVars = mkSSubst . getSVars . S.toList where
  mkSSubst :: [SVar] -> SSubst
  mkSSubst (a:bs) = foldr (\b m -> m <> singleton (b,SVar a)) mempty bs
  getSVars :: [Scale] -> [SVar]
  getSVars = map getSVar . filter isSVar where
    isSVar  (SVar _) = True
    isSVar        _  = False
    getSVar (SVar v) = v

solveBaseConstraints :: Set BaseConstraint -> BSubst
solveBaseConstraints cs = mempty

printScaleInformation :: Set ScaleConstraint -> String
printScaleInformation m =
  let prefix = "{\n"
      content = S.foldr (\x xs -> "  " ++ show x ++ "\n" ++ xs) "" m
      suffix = "}"
  in prefix ++ content ++ suffix

printBaseInformation :: Set BaseConstraint -> String
printBaseInformation m = 
  let prefix = "{\n"
      content = S.foldr (\x xs -> "  " ++ show x ++ "\n" ++ xs) "" m
      suffix = "}"
  in prefix ++ content ++ suffix
  
-- * Scale Substitutions
  
instance Subst (Map SVar Scale) Scale where
  subst m v@(SVar n)   = M.findWithDefault v n m
  subst m   (SMul a b) = SMul (subst m a) (subst m b)
  subst m   (SInv a)   = SInv (subst m a)
  subst m v@_ = v
  
instance (Subst e Scale) => Subst e ScaleConstraint where
  subst m (ScaleEquality ss) = ScaleEquality $ subst m ss

newtype SSubst = SSubst
  { getSSubst :: Map SVar Scale
  } deriving (Eq, Ord, Show)

instance Subst SSubst Scale where
  subst (SSubst m) = subst m
  
instance Subst SSubst SSubst where
  subst m (SSubst s) = SSubst (subst m s)
  
instance Monoid SSubst where
  mempty      = SSubst mempty
  mappend s t = SSubst (getSSubst (subst s t) <> getSSubst (subst t s))
  
instance Singleton SSubst (SVar,Scale) where
  singleton (k,a) = SSubst (M.singleton k a)
  
-- * Base Substitutions

instance Subst (Map BVar Base) Base where
  subst m v@(BVar n) = M.findWithDefault v n m
  subst m v@_ = v
  
instance (Subst e Base) => Subst e BaseConstraint where
  subst m (BaseEquality ss)           = BaseEquality $ subst m ss
  subst m (BasePreservation (x, y) z) = BasePreservation (subst m x, subst m y) (subst m z)
  subst m (BaseSelection (x, y) z)    = BaseSelection (subst m x, subst m y) (subst m z)

newtype BSubst = BSubst
  { getBSubst :: Map BVar Base
  } deriving (Eq, Ord, Show)

instance Subst BSubst Base where
  subst (BSubst m) = subst m

instance Subst BSubst BSubst where
  subst m (BSubst s) = BSubst (subst m s)
  
instance Monoid BSubst where
  mempty      = BSubst mempty
  mappend s t = BSubst (getBSubst (subst s t) <> getBSubst (subst t s))
  
instance Singleton BSubst (BVar,Base) where
  singleton (k,a) = BSubst (M.singleton k a)
