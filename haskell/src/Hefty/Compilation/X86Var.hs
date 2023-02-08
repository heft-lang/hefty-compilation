{-# LANGUAGE GADTs #-}
module Hefty.Compilation.X86Var where

import Hefty

data X86Var c m a where
  X86Var :: X86Var c m (c Int)

instance HFunctor (X86Var c) where
  hmap _ X86Var = X86Var

x86var :: X86Var c << h => Hefty h (c Int)
x86var = send X86Var
