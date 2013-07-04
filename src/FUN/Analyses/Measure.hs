module FUN.Analyses.Measure where

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
  show BNil     = "Unit"
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

-- * Constraint solvers

type SSubst = Map SVar Scale
type BSubst = Map BVar Base

solveScaleConstraints :: Set ScaleConstraint -> SSubst
solveScaleConstraints cs = mempty

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