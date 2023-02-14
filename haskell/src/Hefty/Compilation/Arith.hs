{-# LANGUAGE GADTs #-}
module Hefty.Compilation.Arith where

import Hefty
import Hefty.Compilation.Common

data Arith c m a where
  Add :: c Val -> c Val -> Arith c m (c Val)
  Sub :: c Val -> c Val -> Arith c m (c Val)
  Neg :: c Val -> Arith c m (c Val)
  Int :: Int -> Arith c m (c Val)

instance HFunctor (Arith c) where
  hmap _ (Add x y) = Add x y
  hmap _ (Sub x y) = Sub x y
  hmap _ (Neg x) = Neg x
  hmap _ (Int n) = Int n

add, sub :: Arith c << h => c Val -> c Val -> Hefty h (c Val)
add x y = send (Add x y)
sub x y = send (Sub x y)

neg :: Arith c << h => c Val -> Hefty h (c Val)
neg x = send (Neg x)

int :: Arith c << h => Int -> Hefty h (c Val)
int x = send (Int x)