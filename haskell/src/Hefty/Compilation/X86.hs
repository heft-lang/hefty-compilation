{-# LANGUAGE GADTs, AllowAmbiguousTypes #-}
module Hefty.Compilation.X86 where

import Hefty
import Hefty.Compilation.Common
import Data.Void

data Reg = Rsp | Rbp | Rax | Rbx | Rcx | Rdx | Rsi | Rdi deriving (Eq, Show)

data X86 m a where
  Reg :: Reg -> X86 m (Name Val)
  Deref :: Reg -> Int -> X86 m (Name Val)
  Imm :: Int -> X86 m (Name Val)

  Addq :: Name Val -> Name Val -> X86 m (Name ())
  Subq :: Name Val -> Name Val -> X86 m (Name ())
  Negq :: Name Val -> X86 m (Name ())
  Movq :: Name Val -> Name Val -> X86 m (Name ())

  Callq :: Label -> X86 m (Name ())
  Globl :: Label -> X86 m (Name ())

  Pushq :: Name Val -> X86 m (Name ())
  Popq :: Name Val -> X86 m (Name ())
  Retq :: X86 m a

instance HTraversable X86 where
  htraverse _ (Reg r) = pure $ Reg r
  htraverse _ (Deref r i) = pure $ Deref r i
  htraverse _ (Imm n) = pure $ Imm n
  htraverse _ (Addq x y) = pure $ Addq x y
  htraverse _ (Subq x y) = pure $ Subq x y
  htraverse _ (Negq x) = pure $ Negq x
  htraverse _ (Movq x y) = pure $ Movq x y
  htraverse _ (Callq l) = pure $ Callq l
  htraverse _ (Globl l) = pure $ Globl l
  htraverse _ (Pushq x) = pure $ Pushq x
  htraverse _ (Popq x) = pure $ Popq x
  htraverse _ Retq = pure Retq

reg :: (Fresh < t, X86 << h) => Reg -> TL t h (Name Val)
reg r = sendR (Reg r)

deref :: (Fresh < t, X86 << h) => Reg -> Int -> TL t h (Name Val)
deref r n = sendR (Deref r n)

imm :: (Fresh < t, X86 << h) => Int -> TL t h (Name Val)
imm n = sendR (Imm n)

addq, subq, movq :: (Fresh < t, X86 << h) => Name Val -> Name Val -> TL t h (Name ())
addq x y = sendR (Addq x y)
subq x y = sendR (Subq x y)
movq x y = sendR (Movq x y)

negq :: (Fresh < t, X86 << h) => Name Val -> TL t h (Name ())
negq x = sendR (Negq x)

callq :: (Fresh < t, X86 << h) => Label -> TL t h (Name ())
callq l = sendR (Callq l)

globl :: (Fresh < t, X86 << h) => Label -> TL t h (Name ())
globl lbl = sendR (Globl lbl)

pushq, popq :: (Fresh < t, X86 << h) => Name Val -> TL t h (Name ())
pushq x = sendR (Pushq x)
popq x = sendR (Popq x)

retq :: (Fresh < t, X86 << h) => TL t h (Name a)
retq = sendR Retq

data X86Var m a where
  X86Var :: X86Var m (Name Val)

instance HTraversable X86Var where
  htraverse _ X86Var = pure X86Var

x86var :: (Fresh < t, X86Var << h) => TL t h (Name Val)
x86var = sendR X86Var

data ByteReg = Ah | Al | Bh | Bl | Ch | Cl | Dh | Dl deriving (Eq, Show)

data X86Cond m a where
  ByteReg :: ByteReg -> X86Cond m (Name Val)
  Xorq :: Name Val -> Name Val -> X86Cond m (Name ())
  Cmpq :: Name Val -> Name Val -> X86Cond m (Name ())
  Setcc :: CC -> Name Val -> X86Cond m (Name ())
  Movzbq :: Name Val -> Name Val -> X86Cond m (Name ()) -- 8bit -> 64bit
  Jcc :: CC -> Label -> X86Cond m (Name ())

instance HTraversable X86Cond where
  htraverse _ (ByteReg r) = pure $ ByteReg r
  htraverse _ (Xorq x y) = pure $ Xorq x y
  htraverse _ (Cmpq x y) = pure $ Cmpq x y
  htraverse _ (Setcc cc x) = pure $ Setcc cc x
  htraverse _ (Movzbq x y) = pure $ Movzbq x y
  htraverse _ (Jcc cc l) = pure $ Jcc cc l

byteReg :: (Fresh < t, X86Cond << h) => ByteReg -> TL t h (Name Val)
byteReg r = sendR (ByteReg r)

xorq :: (Fresh < t, X86Cond << h) => Name Val -> Name Val -> TL t h (Name ())
xorq x y = sendR (Xorq x y)

cmpq :: (Fresh < t, X86Cond << h) => Name Val -> Name Val -> TL t h (Name ())
cmpq x y = sendR (Cmpq x y)

setcc :: (Fresh < t, X86Cond << h) => CC -> Name Val -> TL t h (Name ())
setcc cc x = sendR (Setcc cc x)

movzbq :: (Fresh < t, X86Cond << h) => Name Val -> Name Val -> TL t h (Name ())
movzbq x y = sendR (Movzbq x y)

jcc :: (Fresh < t, X86Cond << h) => CC -> Label -> TL t h (Name ())
jcc cc l = sendR (Jcc cc l)