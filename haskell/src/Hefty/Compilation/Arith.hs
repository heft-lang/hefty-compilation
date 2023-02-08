module Hefty.Compilation.Arith where

import Hefty.Algebraic

data Arith c a where
  Add :: c Int -> c Int -> Arith c (c Int)
  Sub :: c Int -> c Int -> Arith c (c Int)
  Neg :: c Int -> Arith c (c Int)
  Int :: Int -> Arith c (c Int)

add, sub :: In eff (Arith c) f => c Int -> c Int -> eff f (c Int)
add x y = lift (Add x y)
sub x y = lift (Sub x y)

neg :: In eff (Arith c) f => c Int -> eff f (c Int)
neg x = lift (Neg x)

int :: In eff (Arith c) f => Int -> eff f (c Int)
int x = lift (Int x)