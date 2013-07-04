{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module FUN.Analyses.Flow where

import FUN.Analyses.Utils

import Data.Monoid
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set,union)
import qualified Data.Set as S

-- * Flow

type FVar = String

-- | Program points.
type Label = String

data Flow 
  = FVar FVar
    deriving (Eq, Ord, Show)
    
-- * Constraint Solving
    
data FlowConstraint
  = Flow String Flow Label
    deriving (Eq, Ord, Show)
    
solveFlowConstraints :: Set FlowConstraint -> Map FVar (String, Set Label)
solveFlowConstraints =
  let mergeNames p q = let (np, cp) = span (/= '.') p
                           (nq, cq) = span (/= '.') q
                       in if np == nq
                             then if cp == cq
                                     then p
                                     else np ++ ".{" ++ tail cp ++ ", " ++ tail cq ++ "}"
                             else error $ "different constructors used to construct sum type (\"" ++ np ++ "\" vs. \"" ++ nq ++ "\")"
      toFEnv (Flow nm (FVar r) l) = M.singleton r (nm, S.singleton l)
  in M.unionsWith (\(nx, vx) (ny, vy) -> (mergeNames nx ny, vx `union` vy) ) . S.toList . S.map toFEnv

printFlowInformation :: Map FVar (String, Set Label) -> String
printFlowInformation m =
  let prefix = "{\n"
      printCon (nm, v) = nm ++ "\t[" ++ (foldr1 (\x xs -> x ++ ", " ++ xs) . S.toList $ v) ++ "]"
      content = M.foldWithKey (\k a as -> "  {" ++ k ++ "}\t~> " ++ printCon a ++ "\n" ++ as) "" m
      suffix = "}"
  in prefix ++ content ++ suffix
  
-- * Substitutions

instance Subst (Map FVar Flow) Flow where
  subst m v@(FVar n) = M.findWithDefault v n m

instance (Subst e Flow) => Subst e FlowConstraint where
  subst m (Flow nm v l) = Flow nm (subst m v) l
