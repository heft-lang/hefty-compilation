{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}
{-# HLINT ignore "Use const" #-}
{-# HLINT ignore "Use >=>" #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

import Hefty hiding (L)
import Hefty.Algebraic
import Prelude hiding (Read, read)

import Hefty.Compilation

arithAlg :: (HFunctor h, Lift (X86 c) << h, Lift (X86Var c) << h) => Alg (Lift (Arith c)) (Hefty h)
arithAlg = Alg \(Lift l) k -> case l of
  Int n -> imm n >>= k
  Add x y -> x86var >>= \z -> movq y z >> addq x z >> k z
  Sub x y -> x86var >>= \z -> movq y z >> subq x z >> k z
  Neg x -> x86var >>= \z -> movq x z >> negq z >> k z

readAlg :: (HFunctor h, Lift (X86 c) << h, Lift (X86Var c) << h) => c Label -> Alg (Lift (Read c)) (Hefty h)
readAlg read_int = Alg \(Lift l) k -> case l of
  Read -> x86var >>= \z -> callq read_int >> reg Rax >>= \rax -> movq rax z >> k z

letAlg :: HFunctor h => Alg (Let c) (Hefty h)
letAlg = Alg \op k -> case op of
  Let m f -> m >>= \x -> f x >>= k

selectInstructions :: forall c h a. (HFunctor h, Lift (X86 c) << h, Lift (X86Var c) << h) =>
  c Label -> Hefty (Lift (Arith c) ++ (Lift (Read c) ++ Let c)) a -> Hefty h a
selectInstructions read_int = foldH pure (arithAlg ++~ readAlg read_int ++~ letAlg)

newtype Const x a = Const { unConst :: x }

countVars :: Alg (Lift (X86Var (Const ()))) (Const Int)
countVars = Alg \(Lift l) k -> case l of
  X86Var -> Const (1 + unConst (k (Const ())))

-- Ideally we would have a version of countvars that ignores all other effects, but writing that generically
-- requires us to modify the Hefty type or introduce a type class to get access to the continuation.

newtype ReaderT r m a = ReaderT { runReaderT :: r -> m a }

assignHomesAlg :: (HFunctor h, Lift (X86 c) << h) => Alg (Lift (X86Var c)) (ReaderT Int (Hefty h))
assignHomesAlg = Alg \(Lift l) k -> case l of
  X86Var -> ReaderT \n -> deref Rbp (-8 * n) >>= \z -> runReaderT (k z) (n + 1)

liftReaderTAlg :: HFunctor h => Alg h m -> Alg h (ReaderT r m)
liftReaderTAlg (Alg a) = Alg \op k -> ReaderT \r -> a (hmap (\z -> runReaderT z r) op) ((\z -> runReaderT z r) . k)

assignHomes :: forall c h a. (HFunctor h, Lift (X86 c) << h) => Hefty (Lift (X86Var c) ++ Lift (X86 c)) a -> Hefty h a
assignHomes x = runReaderT (foldH (ReaderT . const . pure) (assignHomesAlg ++~ liftReaderTAlg nopAlg) x) 1

data Patch c a where
  Mem :: c Int -> Patch c Int
  Loc :: c a -> Patch c a

unpatch :: Patch c a -> c a
unpatch (Mem x) = x
unpatch (Loc x) = x

patchOp :: In eff (X86 c) f => (c Int -> c Int -> eff f a) -> c Int -> c Int -> (() -> eff f b) -> eff f b
patchOp op x y k = reg Rax >>= \z -> movq x z >> op z y >> k ()

patchX86 :: forall h c. (HFunctor h, Lift (X86 c) << h) => Alg (Lift (X86 (Patch c))) (Hefty h)
patchX86 = Alg \(Lift op) k -> case op of
  Addq (Mem x) (Mem y) -> patchOp addq x y k
  Subq (Mem x) (Mem y) -> patchOp subq x y k
  Movq (Mem x) (Mem y) -> patchOp movq x y k

  Reg r -> reg @_ @c r >>= k . Loc
  Deref r i -> deref r i >>= k . Mem
  Imm n -> imm n >>= k . Loc

  Addq x y -> addq (unpatch x) (unpatch y) >>= k
  Subq x y -> subq (unpatch x) (unpatch y) >>= k
  Negq x -> negq (unpatch x) >>= k
  Movq x y -> movq (unpatch x) (unpatch y) >>= k
  Callq l -> callq (unpatch l) >>= k
  Pushq x -> pushq (unpatch x) >>= k
  Popq x -> popq (unpatch x) >>= k
  Retq -> retq @c

patchInstructions :: forall c a. Hefty (Lift (X86 (Patch c))) (Patch c a) -> Hefty (Lift (X86 c)) (c a)
patchInstructions = fmap unpatch . foldH pure patchX86

preludeAndConclusion :: forall c. Int -> Hefty (Lift (X86 c)) (c Int) -> Hefty (Block ++ Lift (X86 c)) ()
preludeAndConclusion stackSize x = do
  rbp <- reg @_ @c Rbp
  rsp <- reg Rsp
  rax <- reg Rax
  n <- imm stackSize
  globl (L "_main")
  blocks
    [ (L "_start", do
      z <- foldH pure nopAlg x
      movq z rax
      jmp (L "_conclusion"))
    , (L "_main", do
      pushq rbp
      movq rsp rbp
      subq n rsp
      jmp (L "_start"))
    , (L "_conclusion", do
      addq n rsp
      popq rbp
      retq @c)
    ]

prettyReg :: Reg -> String
prettyReg Rax = "%rax"
prettyReg Rsp = "%rsp"
prettyReg Rbp = "%rbp"
prettyReg Rbx = "%rbx"
prettyReg Rcx = "%rcx"
prettyReg Rdx = "%rdx"
prettyReg Rdi = "%rdi"
prettyReg Rsi = "%rsi"

prettyX86 :: Alg (Lift (X86 (Const String))) (Const String)
prettyX86 = Alg \(Lift op) k -> case op of
  Reg r -> k $ Const $ prettyReg r
  Deref r i -> k $ Const $ show i ++ "(" ++ prettyReg r ++ ")"
  Imm n -> k $ Const $ "$" ++ show n
  Addq x y -> Const $ "addq " ++ unConst x ++ ", " ++ unConst y ++ "\n" ++ unConst (k ())
  Subq x y -> Const $ "subq " ++ unConst x ++ ", " ++ unConst y ++ "\n" ++ unConst (k ())
  Negq x -> Const $ "negq " ++ unConst x ++ "\n" ++ unConst (k ())
  Movq x y -> Const $ "movq " ++ unConst x ++ ", " ++ unConst y ++ "\n" ++ unConst (k ())
  Callq lab -> Const $ "callq " ++ unConst lab ++ "\n" ++ unConst (k ())

  Pushq x -> Const $ "pushq " ++ unConst x ++ "\n" ++ unConst (k ())
  Popq x -> Const $ "popq " ++ unConst x ++ "\n" ++ unConst (k ())
  Retq -> Const "retq\n"

prettyBlock :: Alg Block (Const String)
prettyBlock = Alg \op k -> case op of
  Blocks blks -> Const $ foldr (\(L lbl, x) xs -> lbl ++ ":\n" ++ unConst x ++ xs) "" blks ++ unConst (k ())
  Jmp (L lbl) -> Const $ "jmp " ++ lbl ++ "\n"
  Globl (L lbl) -> Const $ ".globl " ++ lbl ++ "\n" ++ unConst (k ())

prettyPrint :: Hefty (Block ++ Lift (X86 (Const String))) () -> String
prettyPrint =  unConst . foldH (\_ -> Const "") (prettyBlock ++~ prettyX86)

-- TODO: Use countVars for preludeAndConclusion

main :: IO ()
main = putStrLn $ (prettyPrint . preludeAndConclusion 48 . patchInstructions . assignHomes @(Patch (Const String)) . selectInstructions (Loc (Const "_read_int"))) do
  let' read \y -> do
    z <- read
    w <- neg z
    v <- add y w
    sub y v

-- TODO:
-- [x] Weaken let2set_Alg
-- [x] Change let to have two higher-order arguments
-- [x] Split out common structure of let2set_Alg
-- // [x] Uniquify variables
-- [x] X86Var
-- [x] Stack allocation → X86
-- [ ] Bigger language (e.g. if statement)
-- [ ] Register allocation (dataflow analysis)
-- [ ] Definitional interpreters
-- [ ] Correctness proofs (algebraic laws & definitional interpreters)
-- [ ] How to deal non-local binding (e.g. modules and classes)?
--        Maybe use an abstract binding type (see Jesper's blog) and we may need to change the Hefty tree type.
-- [ ] How to do type checking (on AST or on Hefty tree)? Start with assuming the AST is type checked.