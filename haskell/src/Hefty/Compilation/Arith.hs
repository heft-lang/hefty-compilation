{-# LANGUAGE GADTs #-}
module Hefty.Compilation.Arith where

import Hefty

data Arith c m a where
  Add :: c Int -> c Int -> Arith c m (c Int)
  Sub :: c Int -> c Int -> Arith c m (c Int)
  Neg :: c Int -> Arith c m (c Int)
  Int :: Int -> Arith c m (c Int)

instance HFunctor (Arith c) where
  hmap _ (Add x y) = Add x y
  hmap _ (Sub x y) = Sub x y
  hmap _ (Neg x) = Neg x
  hmap _ (Int n) = Int n

add, sub :: Arith c << h => c Int -> c Int -> Hefty h (c Int)
add x y = send (Add x y)
sub x y = send (Sub x y)

neg :: Arith c << h => c Int -> Hefty h (c Int)
neg x = send (Neg x)

int :: Arith c << h => Int -> Hefty h (c Int)
int x = send (Int x)