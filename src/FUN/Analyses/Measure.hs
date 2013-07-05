-- (C) 2013 Pepijn Kokke & Wout Elsinghorst

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module FUN.Analyses.Measure where

import FUN.Analyses.Utils

import Data.Functor
import Data.Monoid

import Data.Map (Map)
import Data.Set (Set)

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Foldable as F

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
    
-- |Print the semantics of the corresponding constraint. 
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

class Rewrite s where
  rewrite :: s -> s
    
instance Rewrite SSubst where
  rewrite (SSubst r) = SSubst $ M.map rewrite r
    
    
-- |Recursively rewrite Scale expression in an attempt to put them in a normal form. Apart
--  from the obvious cancelations, this algorithm tries to move inverses outwards and re-
--  associates multiplication to the right. Inverses drift towards the right. The idea
--  is that this makes it easier for a future algorithm to perform non-local simplifications
--
--  The rewrite algorithm is called after each round of variable elimination and hopefully
--  creates new opportunities for the next round.
instance Rewrite Scale where
  rewrite (SInv SNil)          = SNil
  rewrite (SInv (SInv a))      = rewrite a
  rewrite (SInv (SMul a b))    = SMul (SInv $ rewrite a) (SInv $ rewrite b)
  
  rewrite (SMul a SNil)        = rewrite a
  rewrite (SMul SNil a)        = rewrite a

  rewrite (SMul a (SInv SNil)) = rewrite a
  rewrite (SMul (SInv SNil) a) = rewrite a
  
  rewrite (SMul a (SInv b))          | a == b = SNil
                                     | otherwise = SMul (rewrite a) (SInv $ rewrite b)
  rewrite (SMul (SInv a) b)          | a == b = SNil
                                     | otherwise = SMul (rewrite b) (SInv $ rewrite a)
  
  rewrite (SMul (SMul a (SInv b)) c) | b == c = rewrite a
                                     | otherwise = SMul (rewrite a) (SMul (rewrite c) (SInv $ rewrite b)) 
  rewrite (SMul (SMul (SInv a) b) c) | a == c = rewrite b
                                     | otherwise = SMul (rewrite b) (SMul (rewrite c) (SInv $ rewrite a)) 

  rewrite (SMul a (SMul b (SInv c))) | a == c = rewrite b
                                     | otherwise = SMul (rewrite a) (SMul (rewrite b) (SInv $ rewrite c))
  rewrite (SMul a (SMul (SInv b) c)) | a == b = rewrite c
                                     | otherwise = SMul (rewrite a) (SMul (rewrite c) (SInv $ rewrite b))
 
  rewrite v@_                  = v

iterationCount :: Int
iterationCount = 16
  
-- |Try to find a substitution that unifies as many Scale constraints as possible.
--  All constraints are equality constraints, and the @solveBaseEquality phase is
--  idempotent. Unfortunately, due to non-linear nesting, not all constraints can
--  be handled in this way. Equality solving is done in different rounds, each 
--  round ending with a rewrite phase that tries to mend the Scale constraints
--  into a normal form. Because this no normal form is guaranteed to be reached,
--  there is a hard coded limit on how rounds to try.
solveScaleConstraints :: Set ScaleConstraint -> SSubst
solveScaleConstraints c = loop iterationCount mempty where  
  loop 0 s0 = s0
  loop n s0 = 
    let s1 = solveScaleEquality $ subst s0 c0
    in loop (n-1) (rewrite $ s1 <> s0)

  filterEquality (ScaleEquality gr) = singleton gr  

  c0 = unionMap filterEquality $ c

  
-- |Iteratively reduce equality constraints until no more reductions are possible.
-- |First
solveScaleEquality:: Set (Set Scale) -> SSubst
solveScaleEquality = loop iterationCount mempty where
  loop 0 s0 _  = s0
  loop n s0 c0 =
    let s1 = F.foldMap solveCons c0
    in if s1 == mempty
          then s0
          else loop (n-1) (s1 <> s0) (subst s1 c0)
   
  solveCons cs = withSingle (single cons) where
    list = S.toList cs
    
    cons = getSCons list
    vars = getSVars list
    
    -- |If there is precisely one definite Scale, take it and unify 
    --  all Scale variables with it. If there are no definite scales
    --  in the equality constraint, try to take a Scale variable and
    --  unify all other variables with it. If there are two or more
    --  definite Scales known then no further unification is possible
    --  at this point.
    single [     ] = SVar <$> maybeHead vars
    single [  x  ] = Just $ x
    single (x:y:_) = Nothing
    
    -- |If one unification step is found, apply it to all Scale variables.
    withSingle (Just  x) = foldr (\v m -> m <> singleton (v,x)) mempty vars
    withSingle (Nothing) = mempty
    
  -- |A list of all definite Scales in this Eq constraint
  getSCons = filter isSCon where
    isSCon  (SNil    ) = True
    isSCon  (SCon _  ) = True
    isSCon  (SInv a  ) = isSCon a
    isSCon  (SMul a b) = isSCon a && isSCon b
    isSCon  (SVar _  ) = False

  -- |A list of all Scale variables in this eq constraint
  getSVars = concatMap $ \t ->
    case t of SVar v -> [v]
              _      -> [ ]
       
-- |Solve Base constraints. The equality case is the same as in the Scale case.
solveBaseConstraints :: Set BaseConstraint -> BSubst
solveBaseConstraints c0 = loop iterationCount mempty where
  loop 0 s0 = s0
  loop n s0 = 
    let c1 = subst s0 . unionMap filterEquality $ c0
        s1 = solveBaseEquality $ c1
      
        c2 = subst (s1 <> s0) . unionMap filterSelection $ c0
        s2 = solveBaseSelection $ c2
      
        c3 = subst (s2 <> s1 <> s0) . unionMap filterPreservation $ c0
        s3 = solveBasePreservation $ c3

    in if s1 == mempty &&
          s2 == mempty &&
          s3 == mempty
          then s0
          else loop (n-1) (s3 <> s2 <> s1 <> s0)

      
  filterEquality  (BaseEquality gr) = singleton gr
  filterEquality _                  = S.empty
  
  filterSelection (BaseSelection (x, y) z) = singleton (x, y, z)
  filterSelection _                        = S.empty

  filterPreservation (BasePreservation (x, y) z) = singleton (x, y, z)
  filterPreservation _                           = S.empty

-- |Constraints added by addition of two variables  
solveBaseSelection :: Set (Base, Base, Base) -> BSubst
solveBaseSelection = F.foldMap solver where
  solver (x, y, BVar z) = if x == BNil
                             then singleton (z, y) 
                             else
                          if y == BNil
                             then singleton (z, x) 
                             else mempty
  solver (BNil, y, z) = case (y, z) of
                          (BVar a, b) -> singleton (a, b)
                          (a, BVar b) -> singleton (b, a)
                          (_,      _) -> mempty
  solver (x, BNil, z) = case (x, z) of
                          (BVar a, b) -> singleton (a, b)
                          (a, BVar b) -> singleton (b, a)
                          (_,      _) -> mempty        

-- |Constraints added by subtraction of two variables  
solveBasePreservation :: Set (Base, Base, Base) -> BSubst
solveBasePreservation = F.foldMap solver where
  solver (x, y, BVar z) = if y == BNil
                             then singleton (z, x) 
                             else
                          if x == y
                             then singleton (z, BNil) 
                             else mempty 
  solver (x, BNil, z) = case (x, z) of
                          (BVar a, b) -> singleton (a, b)
                          (a, BVar b) -> singleton (b, a)
                          (_,      _) -> mempty        

-- |See @solveScaleEquality for details
solveBaseEquality:: Set (Set Base) -> BSubst
solveBaseEquality = loop iterationCount mempty where
  loop 0 s0 _  = s0
  loop n s0 c0 =
    let s1 = F.foldMap solveCons $ subst s0 c0
    in if s1 == mempty
          then s0
          else loop (n-1) (s1 <> s0) (subst s1 c0)
   
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

newtype BSubst = BSubst { 
  getBSubst :: Map BVar Base
  } deriving (Eq, Ord, Show)

instance Subst BSubst Base where
  subst (BSubst m) = subst m

instance Subst BSubst (Base, Base, Base) where
  subst m (a, b, c) = (subst m a, subst m b, subst m c)

  
instance Subst BSubst BSubst where
  subst m (BSubst s) = BSubst (subst m s)
  
instance Monoid BSubst where
  mempty      = BSubst mempty
  mappend s t = BSubst (getBSubst (subst s t) <> getBSubst (subst t s))
  
instance Singleton BSubst (BVar,Base) where
  singleton (k,a) = BSubst (M.singleton k a)
