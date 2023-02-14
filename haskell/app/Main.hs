{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}
{-# HLINT ignore "Use const" #-}
{-# HLINT ignore "Use >=>" #-}

{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE LambdaCase #-}

import Hefty hiding (L)
import Prelude hiding (Read, read, not)

import Hefty.Compilation
import Data.Functor.Const

-- Input language

data L v
  = LInt Int
  | LAdd (L v) (L v)
  | LSub (L v) (L v)
  | LNeg (L v)
  | LRead
  | LLet (L v) (v -> L v)
  | LIf (L v) (L v) (L v)
  | LFalse
  | LTrue
  | LCmp CC (L v) (L v)
  | LNot (L v)
  | LAnd (L v) (L v)
  | LOr (L v) (L v)
  | LVar v

-- Denotation

denote :: (HFunctor h, Arith c << h, Read c << h, Let c << h, Cond c << h) => L (c Val) -> Hefty h (c Val)
denote = \case
  LInt n -> int n
  LAdd x y -> denote x >>= \dx -> denote y >>= \dy -> add dx dy
  LSub x y -> denote x >>= \dx -> denote y >>= \dy -> sub dx dy
  LNeg x -> denote x >>= neg
  LRead -> read
  LLet x f -> let' (denote x) (denote . f)
  LIf c t f -> denote c >>= \dc -> if' dc (denote t) (denote f)
  LFalse -> false
  LTrue -> true
  LCmp cc x y -> denote x >>= \dx -> denote y >>= \dy -> cmp cc dx dy
  LNot x -> denote x >>= not
  LAnd x y -> denote x >>= \dx -> if' dx (denote y) false
  LOr x y -> denote x >>= \dx -> if' dx true (denote y)
  LVar v -> pure v

-- Select Instructions

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

-- TODO: more efficient compilation of if to x86

condAlg :: forall c h. (HFunctor h, X86 c << h, X86Cond c << h, X86Var c << h, Block << h) => Alg (Cond c) (Hefty h)
condAlg = Alg \op k -> case op of
  CIf c t f -> do
    one <- imm @c 1
    z <- x86var
    blocks
      (cmpq c one >> jcc @c Eq (L "_true") >> f >>= \x -> movq x z >> jmp (L "_end"))
      [ (L "_true", t >>= \x -> movq x z)
      , (L "_end", pure ())
      ]
    k z
  CFalse -> imm 0 >>= k
  CTrue -> imm 1 >>= k
  Cmp cc x y -> byteReg Al >>= \al -> x86var >>= \z -> cmpq y x >> setcc cc al >> movzbq al z >> k z
  Not x -> x86var >>= \z -> imm 1 >>= \one -> movq x z >> xorq one z >> k z

selectInstructions :: Label -> Hefty (Arith c ++ Read c ++ Let c ++ Cond c) a -> Hefty (X86Var c ++ X86 c ++ X86Cond c ++ Block) a
selectInstructions read_int = foldH pure (arithAlg ++~ readAlg read_int ++~ letAlg ++~ condAlg)

-- Assign Homes

countVarsAlg :: Alg (X86Var (Const ())) (Const Int)
countVarsAlg = Alg \op k -> case op of
  X86Var -> Const (1 + getConst (k (Const ())))

-- TODO: Generalize countVarsX86Alg

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
  Globl{} -> k ()
  Pushq{} -> k ()
  Popq{} -> k ()
  Retq -> Const 0

countVarsX86CondAlg :: Alg (X86Cond (Const ())) (Const Int)
countVarsX86CondAlg = Alg \op k -> case op of
  ByteReg{} -> k (Const ())
  Xorq{} -> k ()
  Cmpq{} -> k ()
  Setcc{} -> k ()
  Movzbq{} -> k ()
  Jcc{} -> k ()

countVarsBlockAlg :: Alg Block (Const Int)
countVarsBlockAlg = Alg \op k -> case op of
  Blocks b blks -> Const $ getConst b + sum (map (getConst . snd) blks) + getConst (k ())
  Jmp _ -> Const 0

countVars :: Hefty (X86Var (Const ()) ++ X86 (Const ()) ++ X86Cond (Const ()) ++ Block) a -> Int
countVars = getConst . foldH (\_ -> Const 0) (countVarsAlg ++~ countVarsX86Alg ++~ countVarsX86CondAlg ++~ countVarsBlockAlg)

newtype ReaderT r m a = ReaderT (r -> m a)

runReaderT :: r -> ReaderT r m a -> m a
runReaderT r (ReaderT f) = f r

assignHomesAlg :: (HFunctor h, X86 c << h) => Alg (X86Var c) (ReaderT Int (Hefty h))
assignHomesAlg = Alg \op k -> case op of
  X86Var -> ReaderT \n -> deref Rbp (-8 * n) >>= \z -> runReaderT (n + 1) (k z)

liftReaderTAlg :: HFunctor h => Alg h m -> Alg h (ReaderT r m)
liftReaderTAlg (Alg a) = Alg \op k -> ReaderT \r -> a (hmap (runReaderT r) op) (runReaderT r . k)

assignHomes :: Hefty (X86Var c ++ X86 c ++ X86Cond c ++ Block) a -> Hefty (X86 c ++ X86Cond c ++ Block) a
assignHomes x = runReaderT 1 (foldH (ReaderT . const . pure) (assignHomesAlg ++~ liftReaderTAlg injAlg ++~ liftReaderTAlg injAlg ++~ liftReaderTAlg injAlg) x)

-- Patch Instructions

data Patch c a where
  Memory :: c Val -> Patch c Val
  Immediate :: c Val -> Patch c Val
  Other :: c a -> Patch c a

unpatch :: Patch c a -> c a
unpatch (Memory x) = x
unpatch (Immediate x) = x
unpatch (Other x) = x

patchOp :: (HFunctor h, X86 c << h) => (c Val -> c Val -> Hefty h a) -> c Val -> c Val -> (() -> Hefty h b) -> Hefty h b
patchOp op x y k = reg Rax >>= \z -> movq x z >> op z y >> k ()

patchX86 :: forall c h. (HFunctor h, X86 c << h) => Alg (X86 (Patch c)) (Hefty h)
patchX86 = Alg \op k -> case op of
  Addq (Memory x) (Memory y) -> patchOp addq x y k
  Subq (Memory x) (Memory y) -> patchOp subq x y k
  Movq (Memory x) (Memory y) -> patchOp movq x y k

  Reg r -> reg r >>= k . Other
  Deref r i -> deref r i >>= k . Memory
  Imm n -> imm n >>= k . Immediate

  Addq x y -> addq (unpatch x) (unpatch y) >>= k
  Subq x y -> subq (unpatch x) (unpatch y) >>= k
  Negq x -> negq (unpatch x) >>= k
  Movq x y -> movq (unpatch x) (unpatch y) >>= k
  Callq l -> callq @c l >>= k
  Globl l -> globl @c l >>= k
  Pushq x -> pushq (unpatch x) >>= k
  Popq x -> popq (unpatch x) >>= k
  Retq -> retq @c

patchX86Cond :: forall c h. (HFunctor h, X86Cond c << h, X86 c << h) => Alg (X86Cond (Patch c)) (Hefty h)
patchX86Cond = Alg \op k -> case op of
  Xorq (Memory x) (Memory y) -> patchOp xorq x y k
  Cmpq (Memory x) (Memory y) -> patchOp cmpq x y k
  Cmpq x (Immediate y) -> reg Rax >>= \rax -> movq y rax >> cmpq (unpatch x) rax >>= k
  Movzbq x (Memory y) -> reg Rax >>= \rax -> movzbq (unpatch x) rax >> movq rax y >>= k

  ByteReg r -> byteReg r >>= k . Other
  Xorq x y -> xorq (unpatch x) (unpatch y) >>= k
  Cmpq x y -> cmpq (unpatch x) (unpatch y) >>= k
  Setcc cc x -> setcc cc (unpatch x) >>= k
  Movzbq x y -> movzbq (unpatch x) (unpatch y) >>= k
  Jcc cc l -> jcc @c cc l >>= k

patchInstructions :: Hefty (X86 (Patch c) ++ X86Cond (Patch c) ++ Block) (Patch c a) -> Hefty (X86 c ++ X86Cond c ++ Block) (c a)
patchInstructions = fmap unpatch . foldH pure (patchX86 ++~ patchX86Cond ++~ injAlg)

-- Add Prelude and Conclusion

preludeAndConclusion :: forall c. Int -> Hefty (X86 c ++ X86Cond c ++ Block) (c Val) -> Hefty (X86 c ++ X86Cond c ++ Block) ()
preludeAndConclusion varCount x = do
  rbp <- reg @c Rbp
  rsp <- reg Rsp
  rax <- reg Rax
  stackSize <- imm (8 * (varCount + 1 + if even varCount then 1 else 0))
  globl @c (L "_main")
  blocks (pure ())
    [ (L "_start", do
      z <- x
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

-- Pretty Print

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
  Addq x y -> Const $ "\taddq " ++ getConst x ++ ", " ++ getConst y ++ "\n" ++ getConst (k ())
  Subq x y -> Const $ "\tsubq " ++ getConst x ++ ", " ++ getConst y ++ "\n" ++ getConst (k ())
  Negq x -> Const $ "\tnegq " ++ getConst x ++ "\n" ++ getConst (k ())
  Movq x y -> Const $ "\tmovq " ++ getConst x ++ ", " ++ getConst y ++ "\n" ++ getConst (k ())
  Callq lab -> Const $ "\tcallq " ++ getLabel lab ++ "\n" ++ getConst (k ())
  Globl (L lbl) -> Const $ ".globl " ++ lbl ++ "\n" ++ getConst (k ())

  Pushq x -> Const $ "\tpushq " ++ getConst x ++ "\n" ++ getConst (k ())
  Popq x -> Const $ "\tpopq " ++ getConst x ++ "\n" ++ getConst (k ())
  Retq -> Const "\tretq\n"

prettyByteReg :: ByteReg -> String
prettyByteReg = \case
  Ah -> "%ah"
  Al -> "%al"
  Bh -> "%bh"
  Bl -> "%bl"
  Ch -> "%ch"
  Cl -> "%cl"
  Dh -> "%dh"
  Dl -> "%dl"

prettyCC :: CC -> String
prettyCC = \case
  Lt -> "l"
  Le -> "le"
  Eq -> "e"
  Ge -> "ge"
  Gt -> "g"
  Ne -> "ne"

prettyX86Cond :: Alg (X86Cond (Const String)) (Const String)
prettyX86Cond = Alg \op k -> case op of
  ByteReg r -> k $ Const $ prettyByteReg r
  Xorq x y -> Const $ "\txorq " ++ getConst x ++ ", " ++ getConst y ++ "\n" ++ getConst (k ())
  Cmpq x y -> Const $ "\tcmpq " ++ getConst x ++ ", " ++ getConst y ++ "\n" ++ getConst (k ())
  Setcc cc x -> Const $ "\tset" ++ prettyCC cc ++ " " ++ getConst x ++ "\n" ++ getConst (k ())
  Movzbq x y -> Const $ "\tmovzbq " ++ getConst x ++ ", " ++ getConst y ++ "\n" ++ getConst (k ())
  Jcc cc (L lab) -> Const $ "\tj" ++ prettyCC cc ++ " " ++ lab ++ "\n" ++ getConst (k ())

prettyBlock :: Alg Block (Const String)
prettyBlock = Alg \op k -> case op of
  Blocks b blks -> Const $ getConst b ++ foldr (\(L lbl, x) xs -> lbl ++ ":\n" ++ getConst x ++ xs) "" blks ++ getConst (k ())
  Jmp (L lbl) -> Const $ "\tjmp " ++ lbl ++ "\n"

prettyPrint :: Hefty (X86 (Const String) ++ X86Cond (Const String) ++ Block) () -> String
prettyPrint =  getConst . foldH (\_ -> Const "") (prettyX86 ++~ prettyX86Cond ++~ prettyBlock)

-- Main

main :: IO ()
main =
  let
    program :: Hefty (Arith c ++ Read c ++ Let c ++ Cond c) (c Val)
    program = denote $
      LLet LRead \x -> 
        LLet LRead \y -> 
          LIf (LCmp Ge (LVar x) (LVar y))
            (LSub (LVar x) (LVar y))
            (LSub (LVar y) (LVar x))
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