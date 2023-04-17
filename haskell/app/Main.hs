{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# HLINT ignore "Use newtype instead of data" #-}
{-# HLINT ignore "Use const" #-}
{-# HLINT ignore "Use >=>" #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE QuantifiedConstraints #-}

import Data.Functor.Const
import Hefty hiding (L)
import Hefty.Compilation
import Prelude hiding (Read, not, read)
import Data.Bifunctor
import Control.Monad
import qualified Data.Map as Map
import GHC.Exts (Any)
import Unsafe.Coerce
import Data.Kind (Type)

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

denote :: (HTraversable h, Fresh < t, Arith Name << h, Read Name << h, Let << h, Cond Name << h) => L (Name Val) -> TL t h (Name Val)
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

hArith :: (HTraversable h, AlphaEffect h, Alpha a, Fresh < t, X86 << h, X86Var << h) => TL t (Arith Name ++ h) a -> TL t h a
hArith = handleM id pure \op k -> case op of
  Int n -> imm n >>= k
  Add x y -> x86var >>= \z -> movq x z >> addq y z >> k z
  Sub x y -> x86var >>= \z -> movq x z >> subq y z >> k z
  Neg x -> x86var >>= \z -> movq x z >> negq z >> k z

hRead :: forall c h t a. (HTraversable h, AlphaEffect h, Alpha a, Fresh < t, X86 << h, X86Var << h) => Label -> TL t (Read c ++ h) a -> TL t h a
hRead read_int = handleM id pure \op k -> case op of
  Read -> x86var >>= \z -> callq read_int >> reg Rax >>= \rax -> movq rax z >> k z

hLet :: (HTraversable h, AlphaEffect h, Alpha a, Fresh < t) => TL t (Let ++ h) a -> TL t h a
hLet = handleM id pure \op k -> case op of
  Let m v f -> lift (m >>= \x -> rename v x f) >>= k

-- TODO: more efficient compilation of if to x86

hCond :: forall c h t a. (Fresh < t, HTraversable h, Alpha a, AlphaEffect h, X86 << h, X86Cond << h, X86Var << h, Block << h) => TL t (Cond Name ++ h) a -> TL t h a
hCond = handleM id pure \op k -> case op of
  CIf c t f -> do
    one <- imm 1
    z <- x86var
    _ <- blocks
      (cmpq c one >> jcc Eq (L "_true") >> lift f >>= \x -> movq x z >> jmp (L "_end"))
      [ (L "_true", lift t >>= \x -> movq x z),
        (L "_end", unI <$> sendC Fresh)
      ]
    k z
  CFalse -> imm 0 >>= k
  CTrue -> imm 1 >>= k
  Cmp cc x y -> byteReg Al >>= \al -> x86var >>= \z -> cmpq y x >> setcc cc al >> movzbq al z >> k z
  Not x -> x86var >>= \z -> imm 1 >>= \one -> movq x z >> xorq one z >> k z

selectInstructions ::
  ( HTraversable h,
    HTraversable (Read Name ++ (Arith Name ++ h)),
    HTraversable (Arith Name ++ h),
    HTraversable (Let ++ (Read Name ++ (Arith Name ++ h))),
    AlphaEffect h,
    Alpha a,
    Fresh < t,
    X86 << h,
    X86Var << h,
    X86Cond << h,
    Block << h
  ) =>
  Label ->
  TL t (Cond Name ++ (Let ++ (Read Name ++ (Arith Name ++ h)))) a ->
  TL t h a
selectInstructions read_int = hArith . hRead read_int . hLet . hCond

-- Assign Homes

-- data Loc = RegLoc Reg | VarLoc Int | OtherLoc deriving Eq
--
-- uncoverLiveX86Var :: Alg (X86Var (Const Loc)) (ReaderT Int (Const [Loc]))
-- uncoverLiveX86Var = Alg \op k -> case op of
--   X86Var -> ReaderT \n -> runReaderT (n + 1) (k (Const (VarLoc n)))
--
-- uncoverLiveX86 :: Alg (X86 (Const Loc)) (Const [Loc])
-- uncoverLiveX86 = Alg \op k -> case op of
--   Reg r -> k (Const (RegLoc r))
--   Deref{} -> k (Const OtherLoc)
--   Imm{} -> k (Const OtherLoc)
--   _ -> _

-- data Count a where
--   Incr :: Count (I ())
-- 
-- hCount :: TL (Count + h) t a -> TL h t (Int, a)
-- hCount = handleC id (\p x -> lift $ (p,) <$> x) 0 (\p op k ->
--     case op of
--       Incr -> k (p + 1) (I ()))
-- 
-- countVars :: TL t (X86Var ++ h) a -> TL t (X86Var ++ h) (Int, a)
-- countVars = hCount
--   . handleM RH pure (\op k -> case op of X86Var -> sendC Incr *> sendR X86Var >>= k)
--   . weakenC

-- TODO: Generalize countVarsX86Alg

-- countVarsX86Alg :: TL t (X86 ++ h) a -> TL t h a
-- countVarsX86Alg = Alg \op k -> case op of
--   Reg{} -> k (Const ())
--   Deref{} -> k (Const ())
--   Imm{} -> k (Const ())
--   Addq{} -> k ()
--   Subq{} -> k ()
--   Negq{} -> k ()
--   Movq{} -> k ()
--   Callq{} -> k ()
--   Globl{} -> k ()
--   Pushq{} -> k ()
--   Popq{} -> k ()
--   Retq -> Const 0
--
-- countVarsX86CondAlg :: Alg (X86Cond (Const ())) (Const Int)
-- countVarsX86CondAlg = Alg \op k -> case op of
--   ByteReg{} -> k (Const ())
--   Xorq{} -> k ()
--   Cmpq{} -> k ()
--   Setcc{} -> k ()
--   Movzbq{} -> k ()
--   Jcc{} -> k ()
--
-- countVarsBlockAlg :: Alg Block (Const Int)
-- countVarsBlockAlg = Alg \op k -> case op of
--   Blocks b blks -> Const $ getConst b + sum (map (getConst . snd) blks) + getConst (k ())
--   Jmp _ -> Const 0
--
-- countVars :: Hefty (X86Var (Const ()) ++ X86 (Const ()) ++ X86Cond (Const ()) ++ Block) a -> Int
-- countVars = getConst . foldH (\_ -> Const 0) (countVarsAlg ++~ countVarsX86Alg ++~ countVarsX86CondAlg ++~ countVarsBlockAlg)

{-

Note [Stateful folding]

It is not possible to keep track of state during a fold over a Hefty tree.

There are several ways around this:

1. If there are no higher order effects then we can use ReaderT to pass state through into each continuation.
  Unfortunately it is not possible to get access to the result state of a higher order subcomputation.

2. If all operations have unit as their return type then we can use the following "outer state" type:
  newtype OuterState s m a = OuterState (s -> (m a, s))

3. We can convert the whole tree into a first order representation (e.g. using de Bruijn indices).
  Then we can run the stateful pass over that representation. And finally we can convert it back into
  a higher order representation (e.g. (P)HOAS).

4. We can split the statefull pass into two passes: one which computes a distilled delta representation of
  the changes it would apply to whole program and a second one which actually applies that delta.

-}

-- newtype ReaderT r m a = ReaderT (r -> m a)
-- 
-- runReaderT :: r -> ReaderT r m a -> m a
-- runReaderT r (ReaderT f) = f r

data State s a where
  Put :: s -> State s (I ())
  Get :: State s (I s)

hState :: s -> TL (State s + h) t a -> TL h t (s, a)
hState s0 = handleC id (\p x -> lift $ (p,) <$> x) s0 $ \p op k ->
  case op of
    Put p' -> k p' (I ())
    Get -> k p (I p)

assignHomes :: (HTraversable h, AlphaEffect h, Alpha a, Fresh < t, X86 << h) => TL t (X86Var ++ h) a -> TL t h (Int, a)
assignHomes = hState 0 . handleM id pure (\op k -> case op of
  X86Var -> do I n <- sendC Get; z <- deref Rbp (-8 * n); _ <- sendC (Put (n + 1)); k z)
  . weakenC

-- liftReaderTAlg :: HTraversable h => Alg h m -> Alg h (ReaderT r m)
-- liftReaderTAlg (Alg a) = Alg \op k -> ReaderT \r -> a (hmap (runReaderT r) op) (runReaderT r . k)

-- assignHomes :: Hefty (X86Var c ++ X86 c ++ X86Cond c ++ Block) a -> Hefty (X86 c ++ X86Cond c ++ Block) a
-- assignHomes x = runReaderT 1 (foldH (ReaderT . const . pure) (assignHomesAlg ++~ liftReaderTAlg injAlg ++~ liftReaderTAlg injAlg ++~ liftReaderTAlg injAlg) x)

-- Patch Instructions

-- data Patch c a where
--   Memory :: c Val -> Patch c Val
--   Immediate :: c Val -> Patch c Val
--   Other :: c a -> Patch c a
-- 
-- unpatch :: Patch c a -> c a
-- unpatch (Memory x) = x
-- unpatch (Immediate x) = x
-- unpatch (Other x) = x

type NameMap :: (Type -> Type) -> Type
newtype NameMap f = NameMap (Map.Map Int (f Any))

lookupName :: Name a -> NameMap f -> f a
lookupName (Name x) (NameMap m) = unsafeCoerce (m Map.! x)

insertName :: Name a -> f a -> NameMap f -> NameMap f
insertName (Name k) v (NameMap m) = NameMap (Map.insert k (unsafeCoerce v) m)

emptyNameMap :: NameMap f
emptyNameMap = NameMap Map.empty

data AccessType = Memory | Immediate | Other

class HTraversable f => Patch f where
  getAccessType :: f m (Name a) -> AccessType
  patch :: (Fresh < t, X86 << g, Patch g) => (forall m x. f m x -> g m x) -> NameMap (Const AccessType) -> f (HeftyS g) (Name a) -> TL t g (Name a)

instance (Patch f, Patch g) => Patch (f ++ g) where
  getAccessType (LH x) = getAccessType x
  getAccessType (RH x) = getAccessType x
  patch sub m (LH x) = patch (sub . LH) m x
  patch sub m (RH x) = patch (sub . RH) m x

instance Patch X86 where
  getAccessType Imm{} = Immediate
  getAccessType Deref{} = Memory
  getAccessType _ = Other

  patch _ m = \case
    Addq x y | Memory <- m ! x, Memory <- m ! y -> reg Rax >>= \z -> movq x z >> addq z y
    Subq x y | Memory <- m ! x, Memory <- m ! y -> reg Rax >>= \z -> movq x z >> subq z y
    Movq x y | Memory <- m ! x, Memory <- m ! y -> reg Rax >>= \z -> movq x z >> movq z y
    x -> sendR x
    where (!) m k = getConst $ lookupName k m

instance Patch X86Cond where
  getAccessType _ = Other

  patch sub m = \case
    Xorq x y | Memory <- m ! x, Memory <- m ! y -> reg Rax >>= \rax -> movq x rax >> sendSubR sub (Xorq rax y)
    Cmpq x y | Memory <- m ! x, Memory <- m ! y -> reg Rax >>= \rax -> movq x rax >> sendSubR sub (Cmpq rax y)
    Cmpq x y | Immediate <- m ! y -> reg Rax >>= \rax -> movq y rax >> sendSubR sub (Cmpq x rax)
    Movzbq x y | Memory <- m ! y -> reg Rax >>= \rax -> sendSubR sub (Movzbq x rax) >> movq rax y
    x -> sendSubR sub x
    where (!) m k = getConst $ lookupName k m

instance Patch Block where
  getAccessType _ = Other
  patch sub m (Blocks b bs) = do
    b' <- flush (patchHeftyS m b)
    bs' <- traverse (traverse (flush . patchHeftyS m)) bs
    sendSubR sub $ Blocks b' bs'
  patch sub _ (Jmp l) = sendSubR sub $ Jmp l

patchHeftyS :: (Patch h, Fresh < t, X86 << h) => NameMap (Const AccessType) -> HeftyS h a -> TL t h a
patchHeftyS = go where
  go _ (ReturnS x) = pure x
  go m (OpS op n k) = 
    patch id m op >> go (insertName n (Const (getAccessType op)) m) k

patchInstructions :: (Fresh < f, X86 << g, Patch g) => TL f g (Name Val) -> TL f g (Name Val)
patchInstructions = flush >=> patchHeftyS emptyNameMap

-- patchOp :: (HTraversable h, X86 << h) => (c Val -> c Val -> TL t h a) -> c Val -> c Val -> (() -> TL t h b) -> TL t h b
-- patchOp op x y k = reg Rax >>= \z -> movq x z >> op z y >> k ()

-- patchX86 :: forall c h t a. (HTraversable h, X86 << h) => TL t (X86 ++ h) a -> TL t h a
-- patchX86 = Alg \op k -> case op of
--   Addq (Memory x) (Memory y) -> patchOp addq x y k
--   Subq (Memory x) (Memory y) -> patchOp subq x y k
--   Movq (Memory x) (Memory y) -> patchOp movq x y k
--
--   Reg r -> reg r >>= k . Other
--   Deref r i -> deref r i >>= k . Memory
--   Imm n -> imm n >>= k . Immediate
--
--   Addq x y -> addq (unpatch x) (unpatch y) >>= k
--   Subq x y -> subq (unpatch x) (unpatch y) >>= k
--   Negq x -> negq (unpatch x) >>= k
--   Movq x y -> movq (unpatch x) (unpatch y) >>= k
--   Callq l -> callq @c l >>= k
--   Globl l -> globl @c l >>= k
--   Pushq x -> pushq (unpatch x) >>= k
--   Popq x -> popq (unpatch x) >>= k
--   Retq -> retq @c
-- 
-- patchX86Cond :: forall c h t a. (HTraversable h, X86Cond << h, X86 << h) => TL t (X86Cond ++ h) a -> TL t h a
-- patchX86Cond = Alg \op k -> case op of
--   Xorq (Memory x) (Memory y) -> patchOp xorq x y k
--   Cmpq (Memory x) (Memory y) -> patchOp cmpq x y k
--   Cmpq x (Immediate y) -> reg Rax >>= \rax -> movq y rax >> cmpq (unpatch x) rax >>= k
--   Movzbq x (Memory y) -> reg Rax >>= \rax -> movzbq (unpatch x) rax >> movq rax y >>= k
--
--   ByteReg r -> byteReg r >>= k . Other
--   Xorq x y -> xorq (unpatch x) (unpatch y) >>= k
--   Cmpq x y -> cmpq (unpatch x) (unpatch y) >>= k
--   Setcc cc x -> setcc cc (unpatch x) >>= k
--   Movzbq x y -> movzbq (unpatch x) (unpatch y) >>= k
--   Jcc cc l -> jcc @c cc l >>= k

-- patchInstructions :: Hefty (X86 (Patch c) ++ X86Cond (Patch c) ++ Block) (Patch c a) -> Hefty (X86 c ++ X86Cond c ++ Block) (c a)
-- patchInstructions = fmap unpatch . foldH pure (patchX86 ++~ patchX86Cond ++~ injAlg)

-- Add Prelude and Conclusion

preludeAndConclusion :: forall t. (Fresh < t) => Int -> TL t (X86 ++ X86Cond ++ Block) (Name Val) -> TL t (X86 ++ X86Cond ++ Block) (Name ())
preludeAndConclusion varCount x = do
  rbp <- reg Rbp
  rsp <- reg Rsp
  rax <- reg Rax
  stackSize <- imm (8 * (varCount + 2 - (varCount `mod` 2)))
  globl (L "_main")
  blocks
    (unI <$> sendC Fresh)
    [ ( L "_start",
        do
          z <- x
          movq z rax
          jmp (L "_conclusion")
      ),
      ( L "_main",
        do
          pushq rbp
          movq rsp rbp
          subq stackSize rsp
          jmp (L "_start")
      ),
      ( L "_conclusion",
        do
          addq stackSize rsp
          popq rbp
          retq
      )
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

-- prettyX86 :: TL t X86 (Const String)) (Const String)
-- prettyX86 = Alg \op k -> case op of
--   Reg r -> k $ Const $ prettyReg r
--   Deref r i -> k $ Const $ show i ++ "(" ++ prettyReg r ++ ")"
--   Imm n -> k $ Const $ "$" ++ show n
--   Addq x y -> Const $ "\taddq " ++ getConst x ++ ", " ++ getConst y ++ "\n" ++ getConst (k ())
--   Subq x y -> Const $ "\tsubq " ++ getConst x ++ ", " ++ getConst y ++ "\n" ++ getConst (k ())
--   Negq x -> Const $ "\tnegq " ++ getConst x ++ "\n" ++ getConst (k ())
--   Movq x y -> Const $ "\tmovq " ++ getConst x ++ ", " ++ getConst y ++ "\n" ++ getConst (k ())
--   Callq lab -> Const $ "\tcallq " ++ getLabel lab ++ "\n" ++ getConst (k ())
--   Globl (L lbl) -> Const $ ".globl " ++ lbl ++ "\n" ++ getConst (k ())
--
--   Pushq x -> Const $ "\tpushq " ++ getConst x ++ "\n" ++ getConst (k ())
--   Popq x -> Const $ "\tpopq " ++ getConst x ++ "\n" ++ getConst (k ())
--   Retq -> Const "\tretq\n"

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

-- prettyX86Cond :: Alg (X86Cond (Const String)) (Const String)
-- prettyX86Cond = Alg \op k -> case op of
--   ByteReg r -> k $ Const $ prettyByteReg r
--   Xorq x y -> Const $ "\txorq " ++ getConst x ++ ", " ++ getConst y ++ "\n" ++ getConst (k ())
--   Cmpq x y -> Const $ "\tcmpq " ++ getConst x ++ ", " ++ getConst y ++ "\n" ++ getConst (k ())
--   Setcc cc x -> Const $ "\tset" ++ prettyCC cc ++ " " ++ getConst x ++ "\n" ++ getConst (k ())
--   Movzbq x y -> Const $ "\tmovzbq " ++ getConst x ++ ", " ++ getConst y ++ "\n" ++ getConst (k ())
--   Jcc cc (L lab) -> Const $ "\tj" ++ prettyCC cc ++ " " ++ lab ++ "\n" ++ getConst (k ())
--
-- prettyBlock :: Alg Block (Const String)
-- prettyBlock = Alg \op k -> case op of
--   Blocks b blks -> Const $ getConst b ++ foldr (\(L lbl, x) xs -> lbl ++ ":\n" ++ getConst x ++ xs) "" blks ++ getConst (k ())
--   Jmp (L lbl) -> Const $ "\tjmp " ++ lbl ++ "\n"
--
-- prettyPrint :: Hefty (X86 (Const String) ++ X86Cond (Const String) ++ Block) () -> String
-- prettyPrint =  getConst . foldH (\_ -> Const "") (prettyX86 ++~ prettyX86Cond ++~ prettyBlock)

-- Main

main :: IO ()
main =
  let program :: (HTraversable h, Fresh < t, AlphaEffect h, Arith Name << h, Cond Name << h, Read Name << h, Let << h) => TL t h (Name Val)
      program = denote $
        LLet LRead \x ->
          LLet LRead \y ->
            LIf
              (LCmp Ge (LVar x) (LVar y))
              (LSub (LVar x) (LVar y))
              (LSub (LVar y) (LVar x))
      selected :: (Fresh < t) => TL t (X86Var ++ (X86 ++ (X86Cond ++ Block))) (Name Val)
      selected = selectInstructions (L "_read_int") program
      -- I believe this double use of 'selected' will cause the whole pipeline up to that point to be executed twice.
      assigned = assignHomes selected
      full = join $ do
        x <- flush assigned
        let
          (count, _) = extract x
          patched = patchInstructions (fmap snd assigned)
        pure $ preludeAndConclusion count patched
      -- pretty = prettyPrint full
   in pure () -- putStrLn pretty

-- TODO:
-- [x] Weaken let2set_Alg
-- [x] Change let to have two higher-order arguments
-- [x] Split out common structure of let2set_Alg
-- // [x] Uniquify variables
-- [x] X86Var
-- [x] Stack allocation → X86
-- [x] Bigger language (e.g. if statement)
-- [ ] Register allocation (dataflow analysis)
-- [ ] Definitional interpreters
-- [ ] Correctness proofs (algebraic laws & definitional interpreters)
-- [ ] How to deal non-local binding (e.g. modules and classes)?
--        Maybe use an abstract binding type (see Jesper's blog) and we may need to change the Hefty tree type.
-- [ ] How to do type checking (on AST or on Hefty tree)? Start with assuming the AST is type checked.