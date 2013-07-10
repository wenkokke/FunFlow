-- (C) 2013 Pepijn Kokke & Wout Elsinghorst

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module FUN.Analyses.Utils where

import Control.Applicative

import Data.Map (Map)
import Data.Set (Set)

import qualified Data.Map as M
import qualified Data.Set as S

-- * Constraint Solving

class Solver c s | c -> s where
  solveConstraints :: Set c -> (s, Set c)

  
-- * Substitutions

class Subst e w where
  subst :: e -> w -> w
  
instance (Subst e a) => Subst e [a] where
  subst m = map (subst m)

instance (Subst e a, Ord a) => Subst e (Set a) where
  subst m = S.map (subst m)

instance (Subst e a, Ord k) => Subst e (Map k a) where
  subst m = M.map (subst m)
  
-- * Singleton Constructors

class Singleton w k where
  singleton :: k -> w

instance Singleton (Map k a) (k, a) where
  singleton = uncurry M.singleton

instance Singleton (Set k) k where
  singleton = S.singleton  
  
-- * Utility Functions

($*) :: Applicative f => Ord a => Map a b -> a -> f b -> f b
f $* a = \d ->
  case M.lookup a f of
    Just b  -> pure b
    Nothing -> d
    
maybeHead :: [a] -> Maybe a
maybeHead [   ] = Nothing
maybeHead (x:_) = Just x

unionMap :: (Ord a, Ord b) => (a -> Set b) -> Set a -> Set b
unionMap f = S.unions . map f . S.toList

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip fmap

flip2 :: (a -> b -> c) -> (b -> a -> c)
flip2 f = \b a -> f a b
  
flip3 :: (a -> b -> c -> d) -> (b -> c -> a -> d)
flip3 f = \b c a -> f a b c 

flip4 :: (a -> b -> c -> d -> e) -> (b -> c -> d -> a -> e)
flip4 f = \b c d a -> f a b c d 

