module Hefty.Compilation.X86Var where

import Hefty.Algebraic

data X86Var c a where
  X86Var :: X86Var c (c Int)

x86var :: In eff (X86Var c) f => eff f (c Int)
x86var = lift X86Var
