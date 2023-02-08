{-# LANGUAGE GADTs #-}
module Hefty.Compilation.Block where

import Hefty.Compilation.Common
import Hefty

data Block m a where
  Blocks :: [(Label, m ())] -> Block m () 
  Jmp :: Label -> Block m a
  Globl :: Label -> Block m ()

instance HFunctor Block where
  hmap f (Blocks xs) = Blocks (fmap (\(x,y) -> (x, f y)) xs)
  hmap _ (Jmp lbl) = Jmp lbl
  hmap _ (Globl lbl) = Globl lbl

blocks :: Block << h => [(Label, Hefty h ())] -> Hefty h ()
blocks blks = Op (injH $ Blocks blks) Return

jmp :: Block << h => Label -> Hefty h a
jmp lbl = Op (injH $ Jmp lbl) Return

globl :: Block << h => Label -> Hefty h ()
globl lbl = Op (injH $ Globl lbl) Return