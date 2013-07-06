-- (C) 2013 Pepijn Kokke & Wout Elsinghorst

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module FUN.Analyses.Flow where

import FUN.Analyses.Utils

import Data.Monoid

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

import Data.Map (Map)
import Data.Set (Set, union)

-- | Flow Variables
type FVar = String

-- | Program points.
type Label = String

-- |Control Flow Annotation. To keep things Simple, only variables are allowed
data Flow 
  = FVar FVar   -- ^ Flow variable
    deriving (Eq, Ord, Show)
    
-- |Flow constraints generated for Control Flow Analysis 
data FlowConstraint
  = Flow String -- ^ Type of the Program Point (Abs, Fix or some custom product/sum/unit)    
         Flow   -- ^ Annotation Variable associated to a Type
         (Set Label)  -- ^ Program Point that reaches the associated with the Flow variable
    deriving (Eq, Ord, Show)
    
newtype FSubst = FSubst { 
    getFSubst :: Map FVar Flow
  } deriving (Eq, Ord, Show)
 
instance Subst FSubst Flow where
  subst (FSubst m) = subst m
  
instance Subst FSubst FSubst where
  subst m (FSubst s) = FSubst (subst m s)

 
instance Monoid FSubst where
  mempty      = FSubst mempty
  mappend s t = FSubst (getFSubst (subst s t) <> getFSubst (subst t s))

 
-- |Solve the set of flow constraints obtained from the inference algorithm and 
--  obtain a mapping from Flow variables to sets of Program Points. Each flow variable is
--  associated to a specific type that can occur multiple times in the program and each
--  set constains program points that can reach this type.
solveFlowConstraints :: Set FlowConstraint -> (FSubst, Set FlowConstraint)
solveFlowConstraints =
  let mergeNames p q = let (np, cp) = span (/= '.') p
                           (nq, cq) = span (/= '.') q
                       in if np == nq
                             then if cp == cq
                                     then p
                                     else np ++ ".{" ++ tail cp ++ ", " ++ tail cq ++ "}"
                             else error $ "different constructors used to construct sum type (\"" ++ np ++ "\" vs. \"" ++ nq ++ "\")"
      --toFEnv (Flow nm (FVar r) l) = M.singleton r (nm, S.singleton l)
  in  (\r -> (mempty, r))
     . S.fromList . L.map (\(f, (nm, l)) -> Flow nm (FVar f) l)
     . M.toList  
     . M.fromListWithKey  (\f -> \(np, lp) (nq, lq) -> (mergeNames np nq, lp `union` lq) ) 
     . L.map (\(Flow nm (FVar f) l) -> (f, (nm, l)) ) 
     . S.toList 
    
instance Information FlowConstraint FSubst where
  solveConstraints = solveFlowConstraints
    
-- |Pretty print the Annotated Type Variable -> Program Point Set map.
--  Names between brackets correspond to Annotated Type Variables 
--  and Names between brackets correspond to Program Points

printFlowInformation :: Set FlowConstraint -> String
printFlowInformation m =
  let prefix = "{\n"
      printCon (nm, v) = nm ++ "\t[" ++ (foldr1 (\x xs -> x ++ ", " ++ xs) . S.toList $ v) ++ "]"
      content = S.foldr (\(Flow nm (FVar f) v) as -> "  {" ++ f ++ "}\t~> " ++ printCon (nm, v) ++ "\n" ++ as) "" m
      suffix = "}"
  in prefix ++ content ++ suffix
  
-- * Substitutions

instance Subst (Map FVar Flow) Flow where
  subst m v@(FVar n) = M.findWithDefault v n m

instance (Subst e Flow) => Subst e FlowConstraint where
  subst m (Flow nm v l) = Flow nm (subst m v) l
