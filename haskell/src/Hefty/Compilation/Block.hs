{-# LANGUAGE GADTs #-}
module Hefty.Compilation.Block where

import Hefty.Compilation.Common
import Hefty
import Data.Void

data Block m a where
  Blocks :: m (Name ()) -> [(Label, m (Name ()))] -> Block m (Name ()) 
  Jmp :: Label -> Block m a

instance HTraversable Block where
  htraverse f (Blocks x xs) = Blocks <$> f x <*> traverse (\(x,y) -> (x,) <$> f y) xs
  htraverse _ (Jmp lbl) = pure $ Jmp lbl

blocks :: (Fresh < t, Block << h) => TL t h (Name ()) -> [(Label, TL t h (Name ()))] -> TL t h (Name ())
blocks b blks = flush b >>= \b' -> traverse (traverse flush) blks >>= \blks' -> sendR (Blocks b' blks')

jmp :: (Fresh < t, Block << h) => Label -> TL t h (Name a)
jmp lbl = sendR (Jmp lbl)