{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module FUN.Analyses.Utils where

import Control.Applicative

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

-- * Substitutions

class Subst e w where
  subst :: e -> w -> w
  
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
