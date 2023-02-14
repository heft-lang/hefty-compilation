module Hefty.Compilation.Common where

newtype Label = L { getLabel :: String }

data CC = Eq | Ne | Lt | Le | Gt | Ge deriving (Eq, Show)

data Val = VInt Int | VBool Bool