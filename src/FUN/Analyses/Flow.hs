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

-- |Control Flow Annotation. 
data Flow 
  = FVar FVar   -- ^ Flow variable
  | FSet (Set Label)
    deriving (Eq, Ord, Show)
    
-- |Flow constraints generated for Control Flow Analysis 
data FlowConstraint
  = Flow Flow (Set Label)
  | FlowEquality Flow Flow
    deriving (Eq, Ord, Show)
    
newtype FSubst = FSubst { 
    getFSubst :: Map FVar Flow
  } deriving (Eq, Ord, Show)
 
instance Subst FSubst Flow where
  subst (FSubst m) = subst m
  
instance Subst FSubst FSubst where
  subst m (FSubst s) = FSubst (subst m s)

 
instance Monoid FSubst where
  mempty      = FSubst $ mempty
  mappend s t = FSubst $ getFSubst (subst s t) <> getFSubst (subst t s)

 
-- |Solve the set of flow constraints obtained from the inference algorithm and 
--  obtain a mapping from Flow variables to sets of Program Points. Each flow variable is
--  associated to a specific type that can occur multiple times in the program and each
--  set constains program points that can reach this type.
solveFlowConstraints :: Set FlowConstraint -> (FSubst, Set FlowConstraint)
solveFlowConstraints cs = (mempty, cs)
    
instance Solver FlowConstraint FSubst where
  solveConstraints = solveFlowConstraints
    
-- |Pretty print the Annotated Type Variable -> Program Point Set map.
--  Names between brackets correspond to Annotated Type Variables 
--  and Names between brackets correspond to Program Points

printFlowInformation :: Set FlowConstraint -> String
printFlowInformation m =
  let prefix = "{\n"
      printSet v = "[" ++ (foldr1 (\x xs -> x ++ ", " ++ xs) . S.toList $ v) ++ "]"
      printRewrite f v = "  {" ++ f ++ "}\t~> " ++ printSet v ++ "\n"
      content = S.foldr (\r as -> case r of 
                                       Flow (FVar f) v -> printRewrite f v ++ as
                                       FlowEquality (FVar a) (FVar b) -> "  {" ++ a ++ "} ~  {" ++ b ++ "}\n" 
                                       FlowEquality (FVar f) (FSet v) -> printRewrite f v ++ as
                                       FlowEquality (FSet v) (FVar f) -> printRewrite f v ++ as
                                       FlowEquality (FSet p) (FSet q) -> "  " ++ printSet p ++ " ~ " ++ printSet q ++ "\n"
                        ) "" m
      suffix = "}"
  in prefix ++ content ++ suffix
  
-- * Substitutions

instance Subst (Map FVar Flow) Flow where
  subst m v@(FVar n) = M.findWithDefault v n m
  subst m v@(FSet _) = v
  
instance (Subst e Flow) => Subst e FlowConstraint where
  subst m (Flow n l) = Flow (subst m n) l
  subst m (FlowEquality a b) = FlowEquality (subst m a) (subst m b)
  