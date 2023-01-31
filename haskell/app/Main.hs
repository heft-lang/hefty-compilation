{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}
{-# HLINT ignore "Use const" #-}
{-# HLINT ignore "Use >=>" #-}

import Hefty
import Hefty.Algebraic
import Prelude hiding (Read)

data Arith c k
  = Add (c Int) (c Int) (c Int -> k)
  | Sub (c Int) (c Int) (c Int -> k)
  | Mul (c Int) (c Int) (c Int -> k)
  | Int Int (c Int -> k)

add, sub, mul :: (Algebraic eff, In eff (Arith c) f) => c Int -> c Int -> eff f (c Int)
add x y = lift (Add x y)
sub x y = lift (Sub x y)
mul x y = lift (Mul x y)

int :: (Algebraic eff, In eff (Arith c) f) => Int -> eff f (c Int)
int x = lift (Int x)

data Read c k = Read (c Int -> k)

read :: (Algebraic eff, In eff (Read c) f) => eff f (c Int)
read = lift Read

data Let c m k = Let (m (c Int)) (c Int -> m (c Int)) (c Int -> k)

let' :: (Let c << h) => Hefty h (c Int) -> (c Int -> Hefty h (c Int)) -> Hefty h (c Int)
let' m f = Op $ injH $ Let m f Return

data Label

data Reg = Rsp | Rbp | Rax | Rbx | Rcx | Rdx | Rsi | Rdi deriving (Eq, Show)

data X86 c k
  = Reg Reg (c Int -> k)
  | Deref Reg Int (c Int -> k)
  | Imm Int (c Int -> k)
  | Addq (c Int) (c Int) k
  | Subq (c Int) (c Int) k
  | Mulq (c Int) (c Int) k
  | Movq (c Int) (c Int) k
  | Callq (c Label) k

reg :: (Algebraic eff, In eff (X86 c) f) => Reg -> eff f (c Int)
reg r = lift (Reg r)

deref :: (Algebraic eff, In eff (X86 c) f) => Reg -> Int -> eff f (c Int)
deref r n = lift (Deref r n)

imm :: (Algebraic eff, In eff (X86 c) f) => Int -> eff f (c Int)
imm n = lift (Imm n)

addq, subq, mulq, movq :: (Algebraic eff, In eff (X86 c) f) => c Int -> c Int -> eff f ()
addq x y = lift $ \k -> Addq x y (k ())
subq x y = lift $ \k -> Subq x y (k ())
mulq x y = lift $ \k -> Mulq x y (k ())
movq x y = lift $ \k -> Movq x y (k ())

callq :: (Algebraic eff, In eff (X86 c) f) => c Label -> eff f ()
callq l = lift $ \k -> Callq l (k ())

newtype X86Var c k = X86Var (c Int -> k)

x86var :: (Algebraic eff, In eff (X86Var c) f) => eff f (c Int)
x86var = lift X86Var

arithAlg :: (HFunctor h, Lift (X86 c) << h, Lift (X86Var c) << h) => Alg (Lift (Arith c)) (Hefty h)
arithAlg = Alg \(Lift l) -> case l of
  Int n k -> imm n >>= k
  Add x y k -> x86var >>= \z -> movq y z >> addq x z >> k z
  Sub x y k -> x86var >>= \z -> movq y z >> subq x z >> k z
  Mul x y k -> x86var >>= \z -> movq y z >> mulq x z >> k z

readAlg :: (HFunctor h, Lift (X86 c) << h, Lift (X86Var c) << h) => c Label -> Alg (Lift (Read c)) (Hefty h)
readAlg read_int = Alg \(Lift l) -> case l of
  Read k -> x86var >>= \z -> callq read_int >> reg Rax >>= \rax -> movq rax z >> k z

letAlg :: HFunctor h => Alg (Let c) (Hefty h)
letAlg = Alg \case
  Let m f k -> m >>= \x -> f x >>= k

pass1 :: (HFunctor h, Lift (X86 c) << h, Lift (X86Var c) << h) =>
  c Label -> Alg ((Lift (Arith c) ++ Lift (Read c)) ++ Let c) (Hefty h)
pass1 read_int = arithAlg ++~ readAlg read_int ++~ letAlg

-- TODO: implement countvars
-- 
-- countVars : ({op : Op (Lift ε)} → Ret ε op) → Alg (Lift ε) (const ℕ)
-- alg (countVars def) op _ k = 1 + k def

newtype ReaderT r m a = ReaderT { runReaderT :: r -> m a }

assignHomes :: (HFunctor h, Lift (X86 c) << h) => Alg (Lift (X86Var c)) (ReaderT Int (Hefty h))
assignHomes = Alg \(Lift l) -> case l of
  X86Var k -> ReaderT \n -> deref Rbp (-8 * n) >>= \z -> runReaderT (k z) (n + 1)

prettyReg :: Reg -> String
prettyReg Rax = "%rax"
prettyReg Rsp = "%rsp"
prettyReg Rbp = "%rbp"
prettyReg Rbx = "%rbx"
prettyReg Rcx = "%rcx"
prettyReg Rdx = "%rdx"
prettyReg Rdi = "%rdi"
prettyReg Rsi = "%rsi"

-- TODO: implement pretty printing
--
--   pretty-x86 : Alg (Lift X86) (λ _ → String)
--   pretty-x86 = mkAlg λ
--     { (reg r) _ k → k (showReg r)
--     ; (deref r i) _ k → k (ℤShow.show i ++ "(" ++ showReg r ++ ")")
--     ; (imm n) _ k -> ...
--     ; (addq x y) _ k → "addq " ++ x ++ ", " ++ y ++ "\n" ++ k tt
--     ; (subq x y) _ k → "subq " ++ x ++ ", " ++ y ++ "\n" ++ k tt
--     ; (negq x) _ k → "negq " ++ x ++ "\n" ++ k tt
--     ; (movq x y) _ k → "movq " ++ x ++ ", " ++ y ++ "\n" ++ k tt 
--     ; (callq l) _ k → "callq " ++ l ++ "\n" ++ k tt 
--     }

main :: IO ()
main = pure ()

-- TODO:
-- [x] Weaken let2set_Alg
-- [x] Change let to have two higher-order arguments
-- [x] Split out common structure of let2set_Alg
-- // [x] Uniquify variables
-- [x] X86Var
-- [x] Stack allocation → X86
-- [ ] Bigger language (e.g. if statement)
-- [ ] Register allocation (dataflow analysis)
-- [ ] Correctness proofs (algebraic laws & definitional interpreters)
-- [ ] How to deal non-local binding (e.g. modules and classes)?
--        Maybe use an abstract binding type (see Jesper's blog) and we may need to change the Hefty tree type.
-- [ ] How to do type checking (on AST or on Hefty tree)? Start with assuming the AST is type checked.