{-# LANGUAGE GADTs, AllowAmbiguousTypes #-}
module Hefty.Compilation.X86 where

import Hefty
import Hefty.Compilation.Common

data Reg = Rsp | Rbp | Rax | Rbx | Rcx | Rdx | Rsi | Rdi deriving (Eq, Show)

data X86 c m a where
  Reg :: Reg -> X86 c m (c Val)
  Deref :: Reg -> Int -> X86 c m (c Val)
  Imm :: Int -> X86 c m (c Val)

  Addq :: c Val -> c Val -> X86 c m ()
  Subq :: c Val -> c Val -> X86 c m ()
  Negq :: c Val -> X86 c m ()
  Movq :: c Val -> c Val -> X86 c m ()
  Callq :: Label -> X86 c m ()
  Globl :: Label -> X86 c m ()

  Pushq :: c Val -> X86 c m ()
  Popq :: c Val -> X86 c m ()
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
  hmap _ (Globl l) = Globl l
  hmap _ (Pushq x) = Pushq x
  hmap _ (Popq x) = Popq x
  hmap _ Retq = Retq

reg :: X86 c << h => Reg -> Hefty h (c Val)
reg r = send (Reg r)

deref :: X86 c << h => Reg -> Int -> Hefty h (c Val)
deref r n = send (Deref r n)

imm :: X86 c << h => Int -> Hefty h (c Val)
imm n = send (Imm n)

addq, subq, movq :: X86 c << h => c Val -> c Val -> Hefty h ()
addq x y = send (Addq x y)
subq x y = send (Subq x y)
movq x y = send (Movq x y)

negq :: X86 c << h => c Val -> Hefty h ()
negq x = send (Negq x)

callq :: forall c h. X86 c << h => Label -> Hefty h ()
callq l = send (Callq @c l)

globl :: forall c h. X86 c << h => Label -> Hefty h ()
globl lbl = send (Globl @c lbl)

pushq, popq :: X86 c << h => c Val -> Hefty h ()
pushq x = send (Pushq x)
popq x = send (Popq x)

retq :: forall c h a. X86 c << h => Hefty h a
retq = send (Retq @c)

data X86Var c m a where
  X86Var :: X86Var c m (c Val)

instance HFunctor (X86Var c) where
  hmap _ X86Var = X86Var

x86var :: X86Var c << h => Hefty h (c Val)
x86var = send X86Var

data ByteReg = Ah | Al | Bh | Bl | Ch | Cl | Dh | Dl deriving (Eq, Show)

data X86Cond c m a where
  ByteReg :: ByteReg -> X86Cond c m (c Val)
  Xorq :: c Val -> c Val -> X86Cond c m ()
  Cmpq :: c Val -> c Val -> X86Cond c m ()
  Setcc :: CC -> c Val -> X86Cond c m ()
  Movzbq :: c Val -> c Val -> X86Cond c m () -- 8bit -> 64bit
  Jcc :: CC -> Label -> X86Cond c m ()

instance HFunctor (X86Cond c) where
  hmap _ (ByteReg r) = ByteReg r
  hmap _ (Xorq x y) = Xorq x y
  hmap _ (Cmpq x y) = Cmpq x y
  hmap _ (Setcc cc x) = Setcc cc x
  hmap _ (Movzbq x y) = Movzbq x y
  hmap _ (Jcc cc l) = Jcc cc l

byteReg :: X86Cond c << h => ByteReg -> Hefty h (c Val)
byteReg r = send (ByteReg r)

xorq :: X86Cond c << h => c Val -> c Val -> Hefty h ()
xorq x y = send (Xorq x y)

cmpq :: X86Cond c << h => c Val -> c Val -> Hefty h ()
cmpq x y = send (Cmpq x y)

setcc :: X86Cond c << h => CC -> c Val -> Hefty h ()
setcc cc x = send (Setcc cc x)

movzbq :: X86Cond c << h => c Val -> c Val -> Hefty h ()
movzbq x y = send (Movzbq x y)

jcc :: forall c h a. X86Cond c << h => CC -> Label -> Hefty h ()
jcc cc l = send (Jcc @c cc l)