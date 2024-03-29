module Hefty.Compilation.Common where
import Hefty (Alpha (rename))

newtype Label = L { getLabel :: String } deriving (Eq, Ord, Show)

instance Alpha Label where
  rename _ _ x = x

data CC = Eq | Ne | Lt | Le | Gt | Ge deriving (Eq, Show)

data Val = VInt Int | VBool Bool deriving Show