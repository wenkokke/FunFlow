{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module FUN.Analyses.Measure where

import FUN.Analyses.Utils

import Data.Monoid
import Data.Map (Map)
import Data.Functor
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Foldable as F

import Text.Printf (printf)

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
    = "preservation: " ++ show z ++ " = if " ++ show y ++ " = none then " ++ show x 
                                 ++  "; if " ++ show x ++ " = " ++ show y ++ "then none" 
                                 ++  "; else undefined"
  show (BaseSelection (x, y) z)
    = "selection: " ++ show z ++ " = if " ++ show y ++ " = none then " ++ show x
                              ++  "; if " ++ show x ++ " = none then " ++ show y
                              ++  "; else error"

-- * Constraint Solving

isValidScaleConstraint :: ScaleConstraint -> Bool
isValidScaleConstraint (ScaleEquality cs) = S.size cs > 1

class Rewrite s where
  rewrite :: s -> s
    
instance Rewrite SSubst where
  rewrite (SSubst r) = SSubst $ M.map rewrite r
    
instance Rewrite Scale where
  rewrite (SInv SNil)          = SNil
  rewrite (SInv (SMul a b))    = SMul (SInv $ rewrite a) (SInv $ rewrite b)
  rewrite (SInv (SInv a))      = rewrite a
  rewrite (SMul a SNil)        = rewrite a
  rewrite (SMul a (SInv SNil)) = rewrite a
  rewrite (SMul a (SInv b)) | a == b = rewrite a
                            | otherwise = SMul (rewrite a) (SInv $ rewrite b)
  rewrite (SMul a b@(SVar _))  = SMul b (rewrite a) 
  rewrite (SMul (SMul a (SInv b)) c) | b == c = rewrite a
                                     | otherwise = SMul (SMul (rewrite a) (rewrite c)) (SInv $ rewrite b) 
  rewrite (SMul (SInv a) b)    = SMul (rewrite b) (SInv $ rewrite a)
  
  rewrite v@_                  = v


-- complete unification algorithm without thinking about commutativity
-- of the (*) operator, and then "fold" the equality constraints with the
-- unification function.
--
-- then perform one round of imperfect unification across all equality
-- constraints, and apply the result to *all* equality constraints.
--
-- then begin the algorithm anew, and continue for n rounds (because we
-- can't be sure a fixpoint will ever be found).


solveScaleConstraints :: Set ScaleConstraint -> SSubst
solveScaleConstraints c = 
  let filterEquality (ScaleEquality gr) = singleton gr
      c0 = unionMap filterEquality $ c
      s0 = solveScaleEquality $ c0 
  in rewrite s0

solveScaleEquality:: Set (Set Scale) -> SSubst
solveScaleEquality = loop mempty where
  loop s0 c0 =
    let s1 = F.foldMap solveCons c0
    in if s1 == mempty
          then s0
          else loop (s1 <> s0) (subst s1 c0)
   
  solveCons cs = withSingle (single cons) where
    list = S.toList cs
    
    cons = getSCons list
    vars = getSVars list
    
    single [     ] = SVar <$> maybeHead vars
    single [  x  ] = Just $ x
    single (x:y:_) = Nothing
    
    withSingle (Just  x) = foldr (\v m -> m <> singleton (v,x)) mempty vars
    withSingle (Nothing) = mempty
    
  getSCons = filter isSCon where
    isSCon  (SNil    ) = True
    isSCon  (SCon _  ) = True
    isSCon  (SInv a  ) = isSCon a
    isSCon  (SMul a b) = isSCon a && isSCon b
    isSCon  (SVar _  ) = False
    
  getSVars = concatMap $ \t ->
    case t of SVar v -> [v]
              _      -> [ ]
       
solveBaseConstraints :: Set BaseConstraint -> BSubst
solveBaseConstraints c = 
  let filterEquality  (BaseEquality gr) = singleton gr
      filterEquality _                  = S.empty
      
      filterSelection (BaseSelection (x, y) z) = singleton (x, y, z)
      filterSelection _                        = S.empty

      filterPreservation (BasePreservation (x, y) z) = singleton (x, y, z)
      filterPreservation _                           = S.empty

      
      c0 = unionMap filterEquality $ c
      s0 = solveBaseEquality $ c0
      c1 = subst s0 c0
  in s0

solveBaseEquality:: Set (Set Base) -> BSubst
solveBaseEquality = loop mempty where
  loop s0 c0 =
    let s1 = F.foldMap solveCons c0
    in if s1 == mempty
          then s0
          else loop (s1 <> s0) (subst s1 c0)
   
  solveCons cs = withSingle (single cons) where
    list = S.toList cs
    
    cons = getBCons list
    vars = getBVars list
    
    single [     ] = BVar <$> maybeHead vars
    single [  x  ] = Just $ x
    single (x:y:_) = Nothing
    
    withSingle (Just  x) = foldr (\v m -> m <> singleton (v,x)) mempty vars
    withSingle (Nothing) = mempty
    
  getBCons = filter isBCon where
    isBCon  (BNil    ) = True
    isBCon  (BCon _  ) = True
    isBCon  (BVar _  ) = False
    
  getBVars = concatMap $ \t ->
    case t of BVar v -> [v]
              _      -> [ ]


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

newtype SSubst = SSubst { 
    getSSubst :: Map SVar Scale
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
