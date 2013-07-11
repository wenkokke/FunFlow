-- (C) 2013 Pepijn Kokke & Wout Elsinghorst

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module FUN.Analyses.Measure where

import FUN.Analyses.Utils

import Debug.Trace

import Data.Functor
import Data.Monoid
import Data.List

import Data.Map (Map)
import Data.Set (Set)

import Control.Applicative

import qualified Data.List as L
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
  show (SVar v)           = v
  show (SCon c)           = c 
                                              
  show (SMul SNil b)      = show b
  show (SMul a (SInv b))  = "(" ++ show a ++ "/" ++ show b ++ ")"
  show (SMul (SInv a) b)  = "(" ++ show b ++ "/" ++ show a ++ ")"
  show (SMul a b)         = "(" ++ show a ++ "*" ++ show b ++ ")"
  show (SInv a)           = "(1/" ++ show a ++ ")"
   
instance Show Base where
  show BNil     = "None"
  show (BVar v) = "[" ++ v ++ "]"
  show (BCon c) = c

-- * Constraints
  
data ScaleConstraint
  = ScaleEquality (Set Scale)
  deriving (Eq, Ord)
     
instance Show ScaleConstraint where
  show (ScaleEquality ss) = "equality: " ++ (foldr1 (\x xs -> x ++ " ~ " ++ xs) . map show . S.toList $ ss)
  
data BaseConstraint 
  = BaseEquality (Set Base)
  | BasePreservation (Base, Base) Base
  | BaseSelection (Base, Base) Base
  deriving (Eq, Ord)
    
-- |Print the semantics of the corresponding constraint. 
instance Show BaseConstraint where
  show (BaseEquality bs)
    = "equality: " ++ (foldr1 (\x xs -> x ++ " ~ " ++ xs) . map show . S.toList $ bs) 
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
  simplify :: s -> s
    
instance Rewrite ScaleConstraint where
  simplify (ScaleEquality ss) = ScaleEquality $ simplify ss 
    
instance Rewrite SSubst where
  simplify (SSubst r) = SSubst $ M.map simplify r

instance (Rewrite a, Ord a) => Rewrite [a] where
  simplify = map simplify
  
instance (Rewrite a, Ord a) => Rewrite (Set a) where
  simplify = S.map simplify
    
-- |Recursively simplify Scale expression in an attempt to put them in a normal form. Apart
--  from the obvious cancelations, this algorithm tries to move inverses outwards and re-
--  associates multiplication to the right. Inverses drift towards the right. The idea
--  is that this makes it easier for a future algorithm to perform non-local simplifications
--
--  The simplify algorithm is called after each round of variable elimination and hopefully
--  creates new opportunities for the next round.

onlySVars :: Scale -> Bool
onlySVars (SVar _)          = True
onlySVars (SInv (SVar _))   = True
onlySVars (SMul a       (SVar _))   = onlySVars a
onlySVars (SMul a (SInv (SVar _)) ) = onlySVars a
onlySVars _                 = False

isNormal :: Scale -> Bool
isNormal s | onlySVars s           = True
isNormal               (SCon _)    = True
isNormal         (SInv (SCon _))   = True
isNormal (SMul a       (SCon _)  ) = isNormal a
isNormal (SMul a (SInv (SCon _)) ) = isNormal a 

isNormal (SMul a       (SVar _)  ) = onlySVars a
isNormal (SMul a (SInv (SVar _)) ) = onlySVars a

isNormal _                         = False



normalizedInsert :: Scale -> Scale -> Scale
normalizedInsert a@(SInv SNil)     b = b
normalizedInsert a@SNil            b = b

normalizedInsert a@(SInv (SInv x)) b = normalizedInsert x b

normalizedInsert a@(SCon _) b@ SNil       = a
normalizedInsert a@(SCon _) b@(SInv SNil) = a
normalizedInsert a@(SCon _) b             = SMul b a

normalizedInsert a@(SInv (SCon _)) b@ SNil       = a
normalizedInsert a@(SInv (SCon _)) b@(SInv SNil) = a
normalizedInsert a@(SInv (SCon _)) b             = SMul b a

normalizedInsert a@(SInv (SMul x y)) b = normalizedInsert (SInv x) (normalizedInsert (SInv y) b)

normalizedInsert a@(SVar _) b = 
  case b of 
    SNil            -> a
    (SInv SNil)     -> a
    (SCon _)        -> SMul a b
    (SInv (SCon _)) -> SMul a b
    (SVar _)        -> SMul b a
    (SInv (SVar _)) -> SMul b a
    (SMul x y)      -> SMul (normalizedInsert a x) y
  
normalizedInsert a@(SInv (SVar _)) b = 
  case b of 
    SNil            -> a
    (SInv SNil)     -> a
    (SCon _)        -> SMul a b
    (SInv (SCon _)) -> SMul a b
    (SVar _)        -> SMul a b
    (SInv (SVar _)) -> SMul a b
    (SMul x y)      -> SMul (normalizedInsert a x) y

normalizedInsert a@(SMul x y) b = normalizedInsert y (normalizedInsert x b)

normalize t = normalizedInsert t SNil

scaleToList :: Scale -> [Scale]
scaleToList SNil = []
scaleToList a@(SCon _)        = [a]
scaleToList a@(SInv (SCon _)) = [a]
scaleToList a@(SVar _)        = [a]
scaleToList a@(SInv (SVar _)) = [a]
scaleToList (SMul x y) = y : scaleToList x

listToScale :: [Scale] -> Scale
listToScale = foldr (\x xs -> SMul xs x) SNil

splitScale :: Scale -> ([Scale], [Scale])
splitScale s | not (isNormal s) = splitScale (normalize s)
             | otherwise        = span (\t -> case t of 
                                                  (SCon _)      -> True
                                                  SInv (SCon _) -> True
                                                  _             -> False
                                        ) . scaleToList $ s
mergeScale :: ([Scale], [Scale]) -> Scale
mergeScale (s, v) = listToScale $ s ++ v


instance Rewrite Scale where  
  simplify (SInv SNil)          = SNil
  simplify (SInv (SInv a))      = simplify a
  simplify (SInv (SMul a b))    = SMul (simplify $ SInv a) (simplify $ SInv b)
  
  simplify (SMul a SNil)        = simplify a
  simplify (SMul SNil a)        = simplify a

  simplify (SMul a (SInv SNil)) = simplify a
  simplify (SMul (SInv SNil) a) = simplify a
  
  simplify (SMul a (SInv b))    | a == b = SNil 
  simplify (SMul (SInv a) b)    | a == b = SNil
                                     
  simplify (SMul (SMul a (SInv b)) c) | b == c = simplify a
  simplify (SMul (SMul (SInv a) b) c) | a == c = simplify b
  simplify (SMul a (SMul b (SInv c))) | a == c = simplify b
  simplify (SMul a (SMul (SInv b) c)) | a == b = simplify c  

  simplify x@(SMul a b) | not (isNormal x) = normalize x
       
  simplify v@_ = v
      
iterationCount :: Int
iterationCount = 8
  
-- |Try to find a substitution that unifies as many Scale constraints as possible.
--  All constraints are equality constraints, and the @solveBaseEquality phase is
--  idempotent. Unfortunately, due to non-linear nesting, not all constraints can
--  be handled in this way. Equality solving is done in different rounds, each 
--  round ending with a simplify phase that tries to mend the Scale constraints
--  into a normal form. Because this no normal form is guaranteed to be reached,
--  there is a hard coded limit on how rounds to try.
solveScaleConstraints :: Set ScaleConstraint -> (SSubst, Set ScaleConstraint)
solveScaleConstraints = wrap (loop iterationCount mempty)  where   
  loop 0 s0 c0 = (reducer s0, reducer c0)
  loop n s0 c0 = 
    let (s1, c1) = simplifyScaleEquality $ reducer c0
        (    c2) = unionMap unifyScaleEquality $ c1
    in loop (n-1) (s1 <> reducer s0) c2

  reducer :: Rewrite a => a -> a
  reducer = loop 2 where
    loop 0 = id
    loop n = loop (n-1) . simplify
    

  wrap f = pack . f . unpack where  
    pack = fmap (S.map ScaleEquality)
    unpack = S.map (\(ScaleEquality gr) -> gr)

type ScaleEquality = Set Scale

unifyScaleEquality :: ScaleEquality -> Set ScaleEquality
unifyScaleEquality cs =
  let reduceEquality a b = 
        let (conListA, varListA) = splitScale a
            (conListB, varListB) = splitScale b
                                    
            
                    
            simplifiedConList = fmap (reconstruct . getCount) $ names where
              names = nub $ fmap getNames (conListA ++ conListB) where
                getNames s = case s of 
                              SCon nm        -> nm
                              SInv (SCon nm) -> nm

              
              getCount nm = (nm, subCount conListA, subCount conListB) where
                subCount = foldr (\x xs -> case x of
                                              SCon r        -> if nm == r then xs + 1 else xs
                                              SInv (SCon r) -> if nm == r then xs - 1 else xs
                                 ) 0 
              reconstruct (nm, countA, countB) = 
                let diff = countA - countB
                in if diff > 0
                      then (replicate diff $ SCon nm, [])
                      else
                  if diff < 0
                      then ([], replicate (negate diff) $ SCon nm)
                      else ([], [])

            simplifiedVarList = fmap (reconstruct . getCount) $ names where
              names = nub $ fmap getNames (varListA ++ varListB) where
              getNames s = case s of 
                              SVar nm        -> nm
                              SInv (SVar nm) -> nm

              
              getCount nm = (nm, subCount varListA, subCount varListB) where
                subCount = foldr (\x xs -> case x of
                                              SVar r        -> if nm == r then xs + 1 else xs
                                              SInv (SVar r) -> if nm == r then xs - 1 else xs
                                 ) 0 
              reconstruct (nm, countA, countB) = 
                let diff = countA - countB
                in if diff > 0
                      then (replicate diff $ SVar nm, [])
                      else
                  if diff < 0
                      then ([], replicate (negate diff) $ SVar nm)
                      else ([], [])

                      
            simplifiedConListA = concatMap fst simplifiedConList
            simplifiedConListB = concatMap snd simplifiedConList

            simplifiedVarListA = concatMap fst simplifiedVarList
            simplifiedVarListB = concatMap snd simplifiedVarList
  
            mergedA = mergeScale $ (simplifiedConListA, simplifiedVarListA)
            mergedB = mergeScale $ (simplifiedConListB, simplifiedVarListB)
            
            pickyA = if mergedA /= SNil then [mergedA] else [] 
            pickyB = if mergedB /= SNil then [mergedB] else [] 
            
        in S.fromList $ pickyA ++ pickyB
              
  in case S.size cs of
       0 -> S.empty
       1 -> S.empty
       2 -> let [a, b] = S.toList $ cs
            in S.singleton $ reduceEquality a b
       _ -> unionMap unifyScaleEquality $ cs >>~ \a -> 
                                          cs >>~ \b -> if a == b 
                                                          then S.empty 
                                                          else S.singleton $ S.fromList [a, b]

instance Solver ScaleConstraint SSubst where
  solveConstraints = solveScaleConstraints

  
-- |Iteratively reduce equality constraints until no more reductions are possible.
simplifyScaleEquality:: Set ScaleEquality -> (SSubst, Set ScaleEquality)
simplifyScaleEquality = loop mempty where
  loop s0 c0 =
    let s1 = F.foldMap solveCons c0
    in if s1 == mempty
          then (s0, c0)
          else loop (s1 <> s0) (subst s1 c0)
   
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
    single [ ] = case vars of
                       [ ] -> Nothing
                       [x] -> Nothing
                       (x:y:xs) -> Just $ SVar x
    single [x] = Just $ x
    single  _  = Nothing
    
    -- |If one unification step is found, apply it to all Scale variables.
    withSingle (Just  x) = foldr (\v m -> m <> singleton (v,x)) mempty vars
    withSingle (Nothing) = mempty
    
  -- |A list of all definite Scales in this Eq constraint
  getSCons = filter isSCon where
    isSCon  (SNil    ) = True
    isSCon  (SCon _  ) = True
    isSCon  (SInv a  ) = True -- isSCon a
    isSCon  (SMul a b) = True -- isSCon a && isSCon b
    isSCon  (SVar _  ) = False

  -- |A list of all Scale variables in this eq constraint
  getSVars = concatMap $ \t ->
    case t of SVar v -> [v]
              _      -> [ ]
       
-- |Solve Base constraints. The equality case is the same as in the Scale case.
solveBaseConstraints :: Set BaseConstraint -> (BSubst, Set BaseConstraint)
solveBaseConstraints = loop iterationCount mempty where
  loop 0 s0 c0 = (s0, removeSolved c0)
  loop n s0 c0 = 
    let (s1, c1) = solveBaseEquality . unionMap unpackEquality $ c0
        
        (s2, c2) = solveBaseSelection . unionMap unpackSelection $ subst s1 c0
      
        (s3, c3) = solveBasePreservation . unionMap unpackPreservation $ subst (s2 <> s1) c0
                
    in if s1 == mempty &&
          s2 == mempty &&
          s3 == mempty
          then (s0, removeSolved c0)
          else loop (n-1) (s3 <> s2 <> s1 <> s0) (  S.map packEquality     c1
                                                 <> S.map packSelection    c2
                                                 <> S.map packPreservation c3
                                                 )
                                                 
  removeSolved = unionMap (\r -> case r of 
                                   BaseEquality t -> if S.size t == 0 || 
                                                        S.size t == 1 
                                                        then mempty 
                                                        else S.singleton $ BaseEquality t
                
                                   _              -> S.singleton r
                          )
                                              
  unpackEquality  (BaseEquality gr) = singleton gr
  unpackEquality _                  = S.empty
  packEquality = BaseEquality
  
  unpackSelection (BaseSelection (x, y) z) = singleton (x, y, z)
  unpackSelection _                        = S.empty
  packSelection (x, y, z) = BaseSelection (x, y) z
  
  unpackPreservation (BasePreservation (x, y) z) = singleton (x, y, z)
  unpackPreservation _                           = S.empty
  packPreservation (x, y, z) = BasePreservation (x, y) z


instance Solver BaseConstraint BSubst where
  solveConstraints = solveBaseConstraints

type BaseSelection = (Base, Base, Base)
  
-- |Constraints added by addition of two variables  
solveBaseSelection :: Set BaseSelection -> (BSubst, Set BaseSelection)
solveBaseSelection = F.foldMap solver where
  solver r@(x, y, BVar z) = if x == BNil
                               then (singleton (z, y), mempty) 
                               else
                            if y == BNil
                               then (singleton (z, x), mempty) 
                               else (mempty, S.singleton r)
  solver r@(BNil, y, z) = case (y, z) of
                            (BVar a,  b) -> (singleton (a, b), mempty)
                            (a,  BVar b) -> (singleton (b, a), mempty)
                            (BNil, BNil) -> (mempty, mempty)
                            (_,       _) -> (mempty, S.singleton r)
  solver r@(x, BNil, z) = case (x, z) of
                            (BVar a,  b) -> (singleton (a, b), mempty)
                            (a,  BVar b) -> (singleton (b, a), mempty)
                            (BNil, BNil) -> (mempty, mempty)
                            (_,       _) -> (mempty, S.singleton r)        

                            
type BasePreservation = (Base, Base, Base)
                                    
-- |Constraints added by subtraction of two variables  
solveBasePreservation :: Set BasePreservation -> (BSubst, Set BasePreservation)
solveBasePreservation = F.foldMap solver where
  solver r@(x, y, BVar z) = if y == BNil
                               then (singleton (z, x), mempty) 
                               else
                            if x == y
                               then (singleton (z, BNil), mempty) 
                               else (mempty, S.singleton r) 
  solver r@(x, BNil, z) = case (x, z) of
                            (BVar a, b) -> (singleton (a, b), mempty)
                            (a, BVar b) -> (singleton (b, a), mempty)
                            (_,      _) -> (mempty, S.singleton r)        

type BaseEquality = Set Base
                           
                          
-- |See @solveScaleEquality for details
solveBaseEquality:: Set BaseEquality -> (BSubst, Set BaseEquality)
solveBaseEquality = loop mempty where
  loop s0 c0 =
    let s1 = F.foldMap solveCons $ subst s0 c0
    in if s1 == mempty
          then (s0, c0)
          else loop (s1 <> s0) (subst s1 c0)
   
  solveCons cs = withSingle (single cons) where
    list = S.toList cs
    
    cons = getBCons list
    vars = getBVars list
    
    single [     ] = case vars of
                          [ ] -> Nothing
                          [x] -> Nothing
                          (x:y:[]) -> Just $ BVar x
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
    
instance (Subst e Scale) => Subst e ScaleConstraint where
  subst m (ScaleEquality ss) = ScaleEquality $ subst m ss

newtype SSubst = SSubst { 
    getSSubst :: Map SVar Scale
  } deriving (Eq, Ord, Show)

instance Subst SSubst SSubst where
  subst m (SSubst s) = SSubst (subst m s)
  
instance Subst SSubst Scale where
  subst m v@(SVar n)   = M.findWithDefault v n (getSSubst m)
  subst m v@(SCon _)   = v
  subst m   (SMul a b) = SMul (subst m a) (subst m b)
  subst m   (SInv a)   = SInv (subst m a)
  subst m v@_          = v
   
instance Monoid SSubst where
  s `mappend` t = SSubst $ let m = subst s t 
                           in getSSubst (subst m s) `M.union` getSSubst m 
  mempty        = SSubst $ M.empty
                
instance Singleton SSubst (SVar,Scale) where
  singleton (k,a) = SSubst (M.singleton k a)
  
-- * Base Substitutions
  
instance (Subst e Base) => Subst e BaseConstraint where
  subst m (BaseEquality ss)           = BaseEquality $ subst m ss
  subst m (BasePreservation (x, y) z) = BasePreservation (subst m x, subst m y) (subst m z)
  subst m (BaseSelection (x, y) z)    = BaseSelection (subst m x, subst m y) (subst m z)

newtype BSubst = BSubst { 
  getBSubst :: Map BVar Base
  } deriving (Eq, Ord, Show)

instance Subst BSubst BSubst where
  subst m (BSubst s) = BSubst (subst m s)
  
instance Subst BSubst Base where
  subst m v@(BVar n) = M.findWithDefault v n (getBSubst m)
  subst m v@(BCon _) = v
  subst m BNil       = BNil

instance Subst BSubst (Base, Base, Base) where
  subst m (a, b, c) = (subst m a, subst m b, subst m c)
  
instance Monoid BSubst where
  s `mappend` t = BSubst $ let m = subst s t 
                           in getBSubst (subst m s) `M.union` getBSubst m
  mempty        = BSubst $ mempty
  
instance Singleton BSubst (BVar, Base) where
  singleton (k,a) = BSubst (M.singleton k a)
