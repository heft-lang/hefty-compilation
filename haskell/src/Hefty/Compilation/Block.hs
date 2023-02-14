{-# LANGUAGE GADTs #-}
module Hefty.Compilation.Block where

import Hefty.Compilation.Common
import Hefty

data Block m a where
  Blocks :: m () -> [(Label, m ())] -> Block m () 
  Jmp :: Label -> Block m a

instance HFunctor Block where
  hmap f (Blocks x xs) = Blocks (f x) (fmap (\(x,y) -> (x, f y)) xs)
  hmap _ (Jmp lbl) = Jmp lbl

blocks :: Block << h => Hefty h () -> [(Label, Hefty h ())] -> Hefty h ()
blocks b blks = send (Blocks b blks)

jmp :: Block << h => Label -> Hefty h a
jmp lbl = send (Jmp lbl)