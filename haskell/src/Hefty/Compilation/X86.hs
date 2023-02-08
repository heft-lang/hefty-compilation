{-# LANGUAGE AllowAmbiguousTypes #-}
module Hefty.Compilation.X86 where

import Hefty.Algebraic
import Hefty.Compilation.Common

data Reg = Rsp | Rbp | Rax | Rbx | Rcx | Rdx | Rsi | Rdi deriving (Eq, Show)

data X86 c a where
  Reg :: Reg -> X86 c (c Int)
  Deref :: Reg -> Int -> X86 c (c Int)
  Imm :: Int -> X86 c (c Int)
  Addq :: c Int -> c Int -> X86 c ()
  Subq :: c Int -> c Int -> X86 c ()
  Negq :: c Int -> X86 c ()
  Movq :: c Int -> c Int -> X86 c ()
  Callq :: c Label -> X86 c ()

  Pushq :: c Int -> X86 c ()
  Popq :: c Int -> X86 c ()
  Retq :: X86 c a

reg :: In eff (X86 c) f => Reg -> eff f (c Int)
reg r = lift (Reg r)

deref :: In eff (X86 c) f => Reg -> Int -> eff f (c Int)
deref r n = lift (Deref r n)

imm :: In eff (X86 c) f => Int -> eff f (c Int)
imm n = lift (Imm n)

addq, subq, movq :: In eff (X86 c) f => c Int -> c Int -> eff f ()
addq x y = lift (Addq x y)
subq x y = lift (Subq x y)
movq x y = lift (Movq x y)

negq :: In eff (X86 c) f => c Int -> eff f ()
negq x = lift (Negq x)

callq :: In eff (X86 c) f => c Label -> eff f ()
callq l = lift (Callq l)

pushq, popq :: In eff (X86 c) f => c Int -> eff f ()
pushq x = lift (Pushq x)
popq x = lift (Popq x)

retq :: forall c eff f a. In eff (X86 c) f => eff f a
retq = lift (Retq @c)
