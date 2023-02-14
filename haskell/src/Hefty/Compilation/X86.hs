{-# LANGUAGE GADTs, AllowAmbiguousTypes #-}
module Hefty.Compilation.X86 where

import Hefty
import Hefty.Compilation.Common

data Reg = Rsp | Rbp | Rax | Rbx | Rcx | Rdx | Rsi | Rdi deriving (Eq, Show)

data X86 c m a where
  Reg :: Reg -> X86 c m (c Int)
  Deref :: Reg -> Int -> X86 c m (c Int)
  Imm :: Int -> X86 c m (c Int)

  Addq :: c Int -> c Int -> X86 c m ()
  Subq :: c Int -> c Int -> X86 c m ()
  Negq :: c Int -> X86 c m ()
  Movq :: c Int -> c Int -> X86 c m ()
  Callq :: Label -> X86 c m ()

  Pushq :: c Int -> X86 c m ()
  Popq :: c Int -> X86 c m ()
  Retq :: X86 c m a

instance HFunctor (X86 c) where
  hmap _ (Reg r) = Reg r
  hmap _ (Deref r i) = Deref r i
  hmap _ (Imm n) = Imm n
  hmap _ (Addq x y) = Addq x y
  hmap _ (Subq x y) = Subq x y
  hmap _ (Negq x) = Negq x
  hmap _ (Movq x y) = Movq x y
  hmap _ (Callq l) = Callq l
  hmap _ (Pushq x) = Pushq x
  hmap _ (Popq x) = Popq x
  hmap _ Retq = Retq

reg :: X86 c << h => Reg -> Hefty h (c Int)
reg r = send (Reg r)

deref :: X86 c << h => Reg -> Int -> Hefty h (c Int)
deref r n = send (Deref r n)

imm :: X86 c << h => Int -> Hefty h (c Int)
imm n = send (Imm n)

addq, subq, movq :: X86 c << h => c Int -> c Int -> Hefty h ()
addq x y = send (Addq x y)
subq x y = send (Subq x y)
movq x y = send (Movq x y)

negq :: X86 c << h => c Int -> Hefty h ()
negq x = send (Negq x)

callq :: forall c h. X86 c << h => Label -> Hefty h ()
callq l = send (Callq @c l)

pushq, popq :: X86 c << h => c Int -> Hefty h ()
pushq x = send (Pushq x)
popq x = send (Popq x)

retq :: forall c h a. X86 c << h => Hefty h a
retq = send (Retq @c)
