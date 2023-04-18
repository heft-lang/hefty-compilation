{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Hefty.Compilation.Arith where

import Hefty
import Hefty.Compilation.Common

data Arith c m a where
  Add :: c Val -> c Val -> Arith c m (c Val)
  Sub :: c Val -> c Val -> Arith c m (c Val)
  Neg :: c Val -> Arith c m (c Val)
  Int :: Int -> Arith c m (c Val)
deriving instance Show (Arith Name m a)

instance HTraversable (Arith c) where
  htraverse _ (Add x y) = pure $ Add x y
  htraverse _ (Sub x y) = pure $ Sub x y
  htraverse _ (Neg x) = pure $ Neg x
  htraverse _ (Int n) = pure $ Int n


instance (forall x. Alpha (c x)) => Alpha (Arith c m a) where
  rename _ _ (Int k) = Int k
  rename x y (Add z w) = Add (rename x y z) (rename x y w)
  rename x y (Sub z w) = Sub (rename x y z) (rename x y w)
  rename x y (Neg z) = Neg (rename x y z)

add, sub :: (Fresh < t, Arith Name << h) => Name Val -> Name Val -> TL t h (Name Val)
add x y = sendR (Add x y)
sub x y = sendR (Sub x y)

neg :: (Fresh < t, Arith Name << h) => Name Val -> TL t h (Name Val)
neg x = sendR (Neg x)

int :: (Fresh < t, Arith Name << h) => Int -> TL t h (Name Val)
int x = sendR (Int x)