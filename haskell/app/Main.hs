{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}
{-# HLINT ignore "Use const" #-}
{-# HLINT ignore "Use >=>" #-}

{-# LANGUAGE NoMonomorphismRestriction #-}

import Hefty hiding (L)
import Prelude hiding (Read, read)

import Hefty.Compilation
import Data.Functor.Const

arithAlg :: (HFunctor h, X86 c << h, X86Var c << h) => Alg (Arith c) (Hefty h)
arithAlg = Alg \op k -> case op of
  Int n -> imm n >>= k
  Add x y -> x86var >>= \z -> movq x z >> addq y z >> k z
  Sub x y -> x86var >>= \z -> movq x z >> subq y z >> k z
  Neg x -> x86var >>= \z -> movq x z >> negq z >> k z

readAlg :: forall c h. (HFunctor h, X86 c << h, X86Var c << h) => Label -> Alg (Read c) (Hefty h)
readAlg read_int = Alg \op k -> case op of
  Read -> x86var >>= \z -> callq @c read_int >> reg Rax >>= \rax -> movq rax z >> k z

letAlg :: HFunctor h => Alg (Let c) (Hefty h)
letAlg = Alg \op k -> case op of
  Let m f -> m >>= \x -> f x >>= k

selectInstructions :: Label -> Hefty (Arith c ++ Read c ++ Let c) a -> Hefty (X86Var c ++ X86 c) a
selectInstructions read_int = foldH pure (arithAlg ++~ readAlg read_int ++~ letAlg)

countVarsAlg :: Alg (X86Var (Const ())) (Const Int)
countVarsAlg = Alg \op k -> case op of
  X86Var -> Const (1 + getConst (k (Const ())))

-- TODO: Generalize this
countVarsX86Alg :: Alg (X86 (Const ())) (Const Int)
countVarsX86Alg = Alg \op k -> case op of
  Reg{} -> k (Const ())
  Deref{} -> k (Const ())
  Imm{} -> k (Const ())
  Addq{} -> k ()
  Subq{} -> k ()
  Negq{} -> k ()
  Movq{} -> k ()
  Callq{} -> k ()
  Pushq{} -> k ()
  Popq{} -> k ()
  Retq -> Const 0

countVars :: Hefty (X86Var (Const ()) ++ X86 (Const ())) a -> Int
countVars = getConst . foldH (\_ -> Const 0) (countVarsAlg ++~ countVarsX86Alg)

-- Ideally we would have a version of countvars that ignores all other effects, but writing that generically
-- requires us to modify the Hefty type or introduce a type class to get access to the continuation.

newtype ReaderT r m a = ReaderT (r -> m a)

runReaderT :: r -> ReaderT r m a -> m a
runReaderT r (ReaderT f) = f r

assignHomesAlg :: (HFunctor h, X86 c << h) => Alg (X86Var c) (ReaderT Int (Hefty h))
assignHomesAlg = Alg \op k -> case op of
  X86Var -> ReaderT \n -> deref Rbp (-8 * n) >>= \z -> runReaderT (n + 1) (k z)

liftReaderTAlg :: HFunctor h => Alg h m -> Alg h (ReaderT r m)
liftReaderTAlg (Alg a) = Alg \op k -> ReaderT \r -> a (hmap (runReaderT r) op) (runReaderT r . k)

assignHomes :: Hefty (X86Var c ++ X86 c) a -> Hefty (X86 c) a
assignHomes x = runReaderT 1 (foldH (ReaderT . const . pure) (assignHomesAlg ++~ liftReaderTAlg injAlg) x)

data Patch c a where
  Mem :: c Int -> Patch c Int
  Loc :: c a -> Patch c a

unpatch :: Patch c a -> c a
unpatch (Mem x) = x
unpatch (Loc x) = x

patchOp :: (HFunctor h, X86 c << h) => (c Int -> c Int -> Hefty h a) -> c Int -> c Int -> (() -> Hefty h b) -> Hefty h b
patchOp op x y k = reg Rax >>= \z -> movq x z >> op z y >> k ()

patchX86 :: forall c h. (HFunctor h, X86 c << h) => Alg (X86 (Patch c)) (Hefty h)
patchX86 = Alg \op k -> case op of
  Addq (Mem x) (Mem y) -> patchOp addq x y k
  Subq (Mem x) (Mem y) -> patchOp subq x y k
  Movq (Mem x) (Mem y) -> patchOp movq x y k

  Reg r -> reg r >>= k . Loc
  Deref r i -> deref r i >>= k . Mem
  Imm n -> imm n >>= k . Loc

  Addq x y -> addq (unpatch x) (unpatch y) >>= k
  Subq x y -> subq (unpatch x) (unpatch y) >>= k
  Negq x -> negq (unpatch x) >>= k
  Movq x y -> movq (unpatch x) (unpatch y) >>= k
  Callq l -> callq @c l >>= k
  Pushq x -> pushq (unpatch x) >>= k
  Popq x -> popq (unpatch x) >>= k
  Retq -> retq @c

patchInstructions :: Hefty (X86 (Patch c)) (Patch c a) -> Hefty (X86 c) (c a)
patchInstructions = fmap unpatch . foldH pure patchX86

preludeAndConclusion :: forall c. Int -> Hefty (X86 c) (c Int) -> Hefty (Block ++ X86 c) ()
preludeAndConclusion varCount x = do
  rbp <- reg @c Rbp
  rsp <- reg Rsp
  rax <- reg Rax
  stackSize <- imm (8 * (varCount + 1))
  globl (L "_main")
  blocks
    [ (L "_start", do
      z <- foldH pure injAlg x
      movq z rax
      jmp (L "_conclusion"))
    , (L "_main", do
      pushq rbp
      movq rsp rbp
      subq stackSize rsp
      jmp (L "_start"))
    , (L "_conclusion", do
      addq stackSize rsp
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

prettyX86 :: Alg (X86 (Const String)) (Const String)
prettyX86 = Alg \op k -> case op of
  Reg r -> k $ Const $ prettyReg r
  Deref r i -> k $ Const $ show i ++ "(" ++ prettyReg r ++ ")"
  Imm n -> k $ Const $ "$" ++ show n
  Addq x y -> Const $ "addq " ++ getConst x ++ ", " ++ getConst y ++ "\n" ++ getConst (k ())
  Subq x y -> Const $ "subq " ++ getConst x ++ ", " ++ getConst y ++ "\n" ++ getConst (k ())
  Negq x -> Const $ "negq " ++ getConst x ++ "\n" ++ getConst (k ())
  Movq x y -> Const $ "movq " ++ getConst x ++ ", " ++ getConst y ++ "\n" ++ getConst (k ())
  Callq lab -> Const $ "callq " ++ getLabel lab ++ "\n" ++ getConst (k ())

  Pushq x -> Const $ "pushq " ++ getConst x ++ "\n" ++ getConst (k ())
  Popq x -> Const $ "popq " ++ getConst x ++ "\n" ++ getConst (k ())
  Retq -> Const "retq\n"

prettyBlock :: Alg Block (Const String)
prettyBlock = Alg \op k -> case op of
  Blocks blks -> Const $ foldr (\(L lbl, x) xs -> lbl ++ ":\n" ++ getConst x ++ xs) "" blks ++ getConst (k ())
  Jmp (L lbl) -> Const $ "jmp " ++ lbl ++ "\n"
  Globl (L lbl) -> Const $ ".globl " ++ lbl ++ "\n" ++ getConst (k ())

prettyPrint :: Hefty (Block ++ X86 (Const String)) () -> String
prettyPrint =  getConst . foldH (\_ -> Const "") (prettyBlock ++~ prettyX86)

main :: IO ()
main =
  let
    program :: Hefty (Arith c ++ Read c ++ Let c) (c Int)
    program = do
      x <- read
      y <- read
      sub x y
    selected = selectInstructions (L "_read_int") program
    -- I believe this double use of 'selected' will cause the whole pipeline up to that point to be executed twice.
    count = countVars selected
    assigned = assignHomes selected
    patched = patchInstructions assigned
    full = preludeAndConclusion count patched
    pretty = prettyPrint full
  in putStrLn pretty

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