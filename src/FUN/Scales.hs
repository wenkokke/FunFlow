module FUN.Scales where

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
