-- (C) 2013 Pepijn Kokke (3377520) & Wout Elsinghorst (3344819)

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module FUN.Analyses.Flow where

import FUN.Analyses.Utils

import Data.Monoid
import Debug.Trace

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Foldable as F

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
  = FlowEquality Flow Flow
    deriving (Eq, Ord, Show) 

 
-- |Solve the set of flow constraints obtained from the inference algorithm and 
--  obtain a mapping from Flow variables to sets of Program Points. Each flow variable is
--  associated to a specific type that can occur multiple times in the program and each
--  set constains program points that can reach this type.
solveFlowConstraints :: Set FlowConstraint -> (FSubst, Set FlowConstraint)
solveFlowConstraints c0 =
  let (equalities, programPoints, vars, c1) = info where
        info :: (Set (FVar, FVar), [(Label, Set FVar)], Set FVar, Set FlowConstraint)
        info = flip F.foldMap c0 $ \r@(FlowEquality a b) -> 
                                      case (a, b) of 
                                        (FVar a, FVar b) -> (S.singleton (a, b), mempty, S.fromList [a, b], mempty)
                                        (FVar a, FSet l) -> (mempty, map (\l -> (l, S.singleton a) ) (S.toList l), S.singleton a, mempty  )
                                        (FSet l, FVar b) -> (mempty, map (\l -> (l, S.singleton b) ) (S.toList l), S.singleton b, mempty  )
                                        (FSet a, FSet b) -> if a == b then (mempty, mempty, mempty, mempty) 
                                                                      else (mempty, mempty, mempty, S.singleton r)
        
      findReachable :: Set FVar -> Set FVar
      findReachable src = src >>~ \v -> equalities >>~ \(a, b) -> if v == a && not (b `S.member` src)
                                                                     then S.singleton b
                                                                     else
                                                                  if v == b && not (a `S.member` src)
                                                                     then S.singleton a
                                                                     else mempty
        
      
      
      reachables :: Set (Label, Set FVar)
      reachables = S.fromList $ growReachables programPoints where      
        growReachables cs = 
          let round = map (\(nm, v) -> findReachable v) cs
              
              pass = map (S.null) round        
          in if and pass
                then cs
                else growReachables $ zipWith (\(nm, a) b -> (nm, a `S.union` b) ) cs round
      
      findLabels :: FVar -> Set Label
      findLabels v = reachables >>~ \(nm, r) -> if S.member v r
                                                   then S.singleton nm
                                                   else mempty
      
      filterUnreachable = M.mapMaybe $ \a -> case a of FSet l -> if S.null l
                                                                    then Nothing
                                                                    else Just a
                            
      subst = filterUnreachable . flip M.fromSet vars $ \v -> FSet $ findLabels v 
  in (FSubst subst, c1) 
instance Solver FlowConstraint FSubst where
  solveConstraints = solveFlowConstraints
    
-- |Pretty print the Annotated Type Variable -> Program Point Set map.
--  Names between brackets correspond to Annotated Type Variables 
--  and Names between brackets correspond to Program Points

printFlowInformation :: Set FlowConstraint -> String
printFlowInformation m =
  let prefix = "{\n"
      
      printSet v = "[" ++ (foldr1 (\x xs -> x ++ ", " ++ xs) . S.toList $ v) ++ "]" where  
        
      printRewrite f v = "  {" ++ f ++ "}\t~> " ++ printSet v ++ "\n"

      content = S.foldr (\r as -> case r of 
                                       FlowEquality (FVar a) (FVar b) -> "  {" ++ a ++ "}\t~  {" ++ b ++ "}\n" ++ as
                                       FlowEquality (FSet p) (FSet q) -> "  " ++ printSet p ++ " ~ " ++ printSet q ++ "\n" ++ as
                                       FlowEquality (FVar f) (FSet r) -> printRewrite f r ++ as
                                       FlowEquality (FSet r) (FVar f) -> printRewrite f r ++ as
                      ) "" m 
      suffix = "}"
  in prefix ++ content ++ suffix
  
-- * Substitutions
 
instance (Subst e Flow) => Subst e FlowConstraint where
  subst m (FlowEquality a b) = FlowEquality (subst m a) (subst m b)
newtype FSubst = FSubst { 
    getFSubst :: Map FVar Flow
  } deriving (Eq, Ord, Show)
 
instance Subst FSubst Flow where
  subst m v@(FVar n) = M.findWithDefault v n (getFSubst m)
  subst m v@(FSet _) = v
  
instance Subst FSubst FSubst where
  subst m (FSubst q) = FSubst $ subst m q
 
 
    

 
instance Monoid FSubst where
  s `mappend` t = FSubst $ let m = subst s t 
                           in getFSubst (subst m s) `M.union` getFSubst m
  mempty        = FSubst $ mempty
  
instance Singleton FSubst (FVar, Flow) where
  singleton (k,a) = FSubst (M.singleton k a)

  