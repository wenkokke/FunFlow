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
  = ScaleEquality [Scale]
  deriving (Eq, Ord)
     
instance Show ScaleConstraint where
  show (ScaleEquality ss) = "equal: " ++ (foldr1 (\x xs -> x ++ ", " ++ xs) . fmap show $ ss)
  
data BaseConstraint 
  = BaseEquality [Base] 
  | BasePreservation (Base, Base) Base
  | BaseSelection (Base, Base) Base
  deriving (Eq, Ord)
    
instance Show BaseConstraint where
  show (BaseEquality bs)
    = "equal: " ++ (foldr1 (\x xs -> x ++ ", " ++ xs) . fmap show $ bs) 
  show (BasePreservation (x, y) z)
    = "preservation: if " ++ show y ++ " = none then " ++ show x 
                          ++ "; if " ++ show x ++ " = " ++ show y ++ "then none" 
                          ++ "; else undefined"
  show (BaseSelection (x, y) z)
    = "selection: if " ++ show y ++ " = none then " ++ show x
                       ++ "; if " ++ show x ++ " = none then " ++ show y
                       ++ "; else error"

-- * Constraint Solving

type SSubst = Map SVar Scale
type BSubst = Map BVar Base

solveScaleConstraints :: Set ScaleConstraint -> SSubst
solveScaleConstraints cs = mempty

solve1 :: [Scale] -> SSubst
solve1 = ssubst . svars where
  ssubst :: [SVar] -> SSubst
  ssubst (a:bs) = foldr (\b m -> m <> M.singleton b (SVar a)) M.empty bs
  svars :: [Scale] -> [SVar]
  svars = map getSVar . filter isSVar where
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
  
-- * Substitutions
  
instance Subst (Map SVar Scale) Scale where
  subst m v@(SVar n)   = M.findWithDefault v n m
  subst m   (SMul a b) = SMul (subst m a) (subst m b)
  subst m   (SInv a)   = SInv (subst m a)
  subst m v@_ = v

instance Subst (Map BVar Base) Base where
  subst m v@(BVar n) = M.findWithDefault v n m
  subst m v@_ = v
