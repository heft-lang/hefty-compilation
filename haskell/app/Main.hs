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

data Arith c a where
  Add :: c Int -> c Int -> Arith c (c Int)
  Sub :: c Int -> c Int -> Arith c (c Int)
  Neg :: c Int -> Arith c (c Int)
  Int :: Int -> Arith c (c Int)

add, sub :: In eff (Arith c) f => c Int -> c Int -> eff f (c Int)
add x y = lift (Add x y)
sub x y = lift (Sub x y)

neg :: In eff (Arith c) f => c Int -> eff f (c Int)
neg x = lift (Neg x)

int :: In eff (Arith c) f => Int -> eff f (c Int)
int x = lift (Int x)

data Read c a where
  Read :: Read c (c Int)

read :: In eff (Read c) f => eff f (c Int)
read = lift Read

data Let c m k = Let (m (c Int)) (c Int -> m (c Int)) (c Int -> k)
  deriving Functor

instance HFunctor (Let c) where
  hmap f (Let m b k) = Let (f m) (f . b) k

let' :: (Let c << h) => Hefty h (c Int) -> (c Int -> Hefty h (c Int)) -> Hefty h (c Int)
let' m f = Op $ injH $ Let m f Return

data Label = L String

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

-- label :: In eff (X86 c) f => String -> eff f (c Label)
-- label l = lift (Label l)

-- globl, block :: In eff (X86 c) f => c Label -> eff f ()
-- globl l = lift (Globl l)
-- block l = lift (Block l)

pushq, popq :: In eff (X86 c) f => c Int -> eff f ()
pushq x = lift (Pushq x)
popq x = lift (Popq x)

-- jmp :: In eff (X86 c) f => c Label -> eff f ()
-- jmp l = lift (Jmp l)

retq :: forall c eff f a. In eff (X86 c) f => eff f a
retq = lift (Retq @c)

data Block m k
  = Blocks [(Label, m ())] k
  | Jmp Label
  | Globl Label k
  deriving Functor

instance HFunctor Block where
  hmap f (Blocks xs k) = Blocks (fmap (\(x,y) -> (x, f y)) xs) k
  hmap _ (Jmp lbl) = Jmp lbl
  hmap _ (Globl lbl k) = Globl lbl k

blocks :: Block << h => [(Label, Hefty h ())] -> Hefty h ()
blocks blks = Op $ injH $ Blocks blks (Return ())

jmp :: Block << h => Label -> Hefty h a
jmp lbl = Op $ injH $ Jmp lbl

globl :: Block << h => Label -> Hefty h ()
globl lbl = Op $ injH $ Globl lbl (Return ())

data X86Var c a where
  X86Var :: X86Var c (c Int)

x86var :: In eff (X86Var c) f => eff f (c Int)
x86var = lift X86Var

arithAlg :: (HFunctor h, Lift (X86 c) << h, Lift (X86Var c) << h) => Alg (Lift (Arith c)) (Hefty h)
arithAlg = Alg \(Lift l k) -> case l of
  Int n -> imm n >>= k
  Add x y -> x86var >>= \z -> movq y z >> addq x z >> k z
  Sub x y -> x86var >>= \z -> movq y z >> subq x z >> k z
  Neg x -> x86var >>= \z -> movq x z >> negq z >> k z

readAlg :: (HFunctor h, Lift (X86 c) << h, Lift (X86Var c) << h) => c Label -> Alg (Lift (Read c)) (Hefty h)
readAlg read_int = Alg \(Lift l k) -> case l of
  Read -> x86var >>= \z -> callq read_int >> reg Rax >>= \rax -> movq rax z >> k z

letAlg :: HFunctor h => Alg (Let c) (Hefty h)
letAlg = Alg \case
  Let m f k -> m >>= \x -> f x >>= k

pass1 :: forall c h a. (HFunctor h, Lift (X86 c) << h, Lift (X86Var c) << h) =>
  c Label -> Hefty (Lift (Arith c) ++ (Lift (Read c) ++ Let c)) a -> Hefty h a
pass1 read_int = foldH pure (arithAlg ++~ readAlg read_int ++~ letAlg)

newtype Const x a = Const { unConst :: x }


countVars :: Alg (Lift (X86Var (Const ()))) (Const Int)
countVars = Alg \(Lift l k) -> case l of
  X86Var -> Const (1 + unConst (k (Const ())))

-- Ideally we would have a version of countvars that ignores all other effects, but writing that generically
-- requires us to modify the Hefty type or introduce a type class to get access to the continuation.

newtype ReaderT r m a = ReaderT { runReaderT :: r -> m a }

assignHomes :: (HFunctor h, Lift (X86 c) << h) => Alg (Lift (X86Var c)) (ReaderT Int (Hefty h))
assignHomes = Alg \(Lift l k) -> case l of
  X86Var -> ReaderT \n -> deref Rbp (-8 * n) >>= \z -> runReaderT (k z) (n + 1)

liftReaderTAlg :: (HFunctor h, Functor (h (ReaderT r m))) => Alg h m -> Alg h (ReaderT r m)
liftReaderTAlg (Alg x) = Alg \y -> ReaderT \r -> x (hmap (\z -> runReaderT z r) $ fmap (\z -> runReaderT z r) $ y)

pass2 :: forall c h a. (HFunctor h, Lift (X86 c) << h) => Hefty (Lift (X86Var c) ++ Lift (X86 c)) a -> Hefty h a
pass2 x = runReaderT (foldH (ReaderT . const . pure) (assignHomes ++~ liftReaderTAlg nopAlg) x) 1

data Patch c a where
  Mem :: c Int -> Patch c Int
  Loc :: c a -> Patch c a

unpatch :: Patch c a -> c a
unpatch (Mem x) = x
unpatch (Loc x) = x

patchOp :: In eff (X86 c) f => (c Int -> c Int -> eff f a) -> c Int -> c Int -> (() -> eff f b) -> eff f b
patchOp op x y k = reg Rax >>= \z -> movq x z >> op z y >> k ()

patchX86 :: forall h c. (HFunctor h, Lift (X86 c) << h) => Alg (Lift (X86 (Patch c))) (Hefty h)
patchX86 = Alg \(Lift op k) -> case op of
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

pass25 :: forall c a. Hefty (Lift (X86 (Patch c))) (Patch c a) -> Hefty (Lift (X86 c)) (c a)
pass25 = fmap unpatch . foldH pure patchX86

pass3 :: forall c. Int -> Hefty (Lift (X86 c)) (c Int) -> Hefty (Block ++ Lift (X86 c)) ()
pass3 stackSize x = do
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
prettyX86 = Alg \(Lift op k) -> case op of
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
prettyBlock = Alg \case
  Blocks blks k -> Const $ foldr (\(L lbl, x) xs -> lbl ++ ":\n" ++ unConst x ++ xs) "" blks ++ unConst k
  Jmp (L lbl) -> Const $ "jmp " ++ lbl ++ "\n"
  Globl (L lbl) k -> Const $ ".globl " ++ lbl ++ "\n" ++ unConst k

pass4 :: Hefty (Block ++ Lift (X86 (Const String))) () -> String
pass4 =  unConst . foldH (\_ -> Const "") (prettyBlock ++~ prettyX86)

-- TODO: Use countVars for pass3

main :: IO ()
main = putStrLn $ (pass4 . pass3 48 . pass25 . pass2 @(Patch (Const String)) . pass1 (Loc (Const "_read_int"))) do
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
-- [ ] Correctness proofs (algebraic laws & definitional interpreters)
-- [ ] How to deal non-local binding (e.g. modules and classes)?
--        Maybe use an abstract binding type (see Jesper's blog) and we may need to change the Hefty tree type.
-- [ ] How to do type checking (on AST or on Hefty tree)? Start with assuming the AST is type checked.