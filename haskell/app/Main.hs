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
import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import GHC.Exts (Any)
import Unsafe.Coerce
import Data.Kind (Type)
import Data.List (intercalate)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)

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
  LAdd x y -> do
    dx <- denote x
    dy <- denote y
    add dx dy
  LSub x y -> do
    dx <- denote x
    dy <- denote y
    sub dx dy
  LNeg x -> do
    dx <- denote x
    neg dx

  LRead -> read

  LLet x f ->
    let' (denote x) $ \vx ->
      denote (f vx)

  LIf c t f -> do
    dc <- denote c
    if' dc (denote t) (denote f)
  LFalse -> false
  LTrue -> true
  LCmp cc x y -> do
    dx <- denote x
    dy <- denote y
    cmp cc dx dy
  LNot x -> do
    dx <- denote x
    not dx
  LAnd x y -> do
    dx <- denote x
    if' dx (denote y) false
  LOr x y -> do
    dx <- denote x
    if' dx true (denote y)
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

hCond :: forall h t a. (Fresh < t, HTraversable h, Alpha a, AlphaEffect h, X86 << h, X86Cond << h, X86Var << h, Block << h) => TL t (Cond Name ++ h) a -> TL t h a
hCond = handleM id pure \op k -> case op of
  CIf c t f -> do
    one <- imm 1
    z <- x86var
    _ <- blocks
      [ (L "_cond", cmpq c one >> jcc Eq (L "_true") >> lift f >>= \x -> movq x z >> jmp (L "_end")),
        (L "_true", lift t >>= \x -> movq x z),
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


-- Uncover Live

-- Liveness analysis is a backwards dataflow analysis. This could perhaps be captures as a backwards state monad.
-- but the backwards state monad cannot be written as a freer monad over some functor (at least if it is combined with other functors).
-- However, we can use a writer which writes state updates as endomorphisms on the state and compose them backwards.

-- I should make a type class which allows compiler writers to define how operations affect the live set.
-- Then like patchInstructions, I can fold over the program.

class Live f where
  live :: Live g => f (HeftyS g) (Name a) -> Map Label (Set (Either Reg (Name Val))) -> Set (Either Reg (Name Val)) -> Set (Either Reg (Name Val))

callerSaved :: Set (Either Reg (Name Val))
callerSaved = Set.fromList $ map Left [Rax, Rcx, Rdx, Rsi, Rdi, R8, R9, R10, R11]

calleeSaved :: Set (Either Reg (Name Val))
calleeSaved = Set.fromList $ map Left [Rbp, Rbx, R12, R13, R14, R15]

funArg :: [Reg]
funArg = [Rsi, Rdx, Rcx, R8, R9]

instance Live X86 where
  live (Movq x y) _ = Set.insert (Right x) . Set.delete (Right y)
  live (Addq x y) _ = Set.insert (Right x) . Set.insert (Right y)
  live (Subq x y) _ = Set.insert (Right x) . Set.insert (Right y)
  live (Negq x) _ = Set.insert (Right x)
  live (Pushq x) _ = Set.insert (Right x)
  live (Popq x) _ = Set.delete (Right x)
  live (Callq _) _ = Set.union calleeSaved . Set.difference callerSaved
  live Reg{} _ = id
  live Deref{} _ = id
  live Imm{} _ = id
  live Retq{} _ = id
  live Globl{} _ = id

instance Live X86Var where
  live X86Var _ = id

instance Live X86Cond where
  live (Movzbq x y) _ = Set.insert (Right x) . Set.delete (Right y)
  live (Xorq x y) _ = Set.insert (Right x) . Set.insert (Right y)
  live (Cmpq x y) _ = Set.insert (Right x) . Set.insert (Right y)
  live (Setcc _ x) _ = Set.delete (Right x)
  live (Jcc _ l) m = maybe id Set.union (Map.lookup l m)
  live ByteReg{} _ = id

instance Live Block where
  live (Blocks []) _ s0 = s0
  live (Blocks bs) m0 s0 = (Map.! fst (head bs)) $ loop m0 where
    loop m
      | m == m' = m
      | otherwise = loop m'
      where
        m' = Map.unionWith Set.union m (Map.fromList (let ss = zipWith (\(l,h) s2 -> (l, liveHefty h m s2)) bs (tail (map snd ss) ++ [s0]) in ss))
  live (Jmp l) m _ = fromMaybe Set.empty (Map.lookup l m)

liveHefty :: Live f => HeftyS f a -> Map Label (Set (Either Reg (Name Val))) -> Set (Either Reg (Name Val)) -> Set (Either Reg (Name Val))
liveHefty = undefined


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
newtype NameMap f = NameMap (Map Int (f Any))

lookupName :: Name a -> NameMap f -> f a
lookupName (Name x) (NameMap m) = unsafeCoerce (m Map.! x)

insertName :: Name a -> f a -> NameMap f -> NameMap f
insertName (Name k) v (NameMap m) = NameMap (Map.insert k (unsafeCoerce v) m)

emptyNameMap :: NameMap f
emptyNameMap = NameMap Map.empty

data AccessType = Memory | Immediate | Other

class HTraversable f => Patch f where
  getAccessType :: f m (Name a) -> AccessType
  patch :: (Fresh < t, X86 << g, Patch g, AlphaEffect g) => (forall m x. f m x -> g m x) -> NameMap (Const AccessType) -> f (HeftyS g) (Name a) -> TL t g (Name a)

instance (Patch f, Patch g) => Patch (f ++ g) where
  getAccessType (LH x) = getAccessType x
  getAccessType (RH x) = getAccessType x
  patch sub m (LH x) = patch (sub . LH) m x
  patch sub m (RH x) = patch (sub . RH) m x

instance Patch X86 where
  getAccessType Imm{} = Immediate
  getAccessType Deref{} = Memory
  getAccessType _ = Other

  patch sub m = \case
    Addq x y | Memory <- m ! x, Memory <- m ! y -> reg Rax >>= \z -> movq x z >> addq z y
    Subq x y | Memory <- m ! x, Memory <- m ! y -> reg Rax >>= \z -> movq x z >> subq z y
    Movq x y | Memory <- m ! x, Memory <- m ! y -> reg Rax >>= \z -> movq x z >> movq z y
    x -> sendSubR sub x
    where m ! k = getConst $ lookupName k m

instance Patch X86Cond where
  getAccessType _ = Other

  patch sub m = \case
    Xorq x y | Memory <- m ! x, Memory <- m ! y -> reg Rax >>= \rax -> movq x rax >> sendSubR sub (Xorq rax y)
    Cmpq x y | Memory <- m ! x, Memory <- m ! y -> reg Rax >>= \rax -> movq x rax >> sendSubR sub (Cmpq rax y)
    Cmpq x y | Immediate <- m ! y -> reg Rax >>= \rax -> movq y rax >> sendSubR sub (Cmpq x rax)
    Movzbq x y | Memory <- m ! y -> reg Rax >>= \rax -> sendSubR sub (Movzbq x rax) >> movq rax y
    x -> sendSubR sub x
    where m ! k = getConst $ lookupName k m

instance Patch Block where
  getAccessType _ = Other
  patch sub m (Blocks bs) = do
    bs' <- traverse (traverse (flush . patchHeftyS m)) bs
    sendSubR sub $ Blocks bs'
  patch sub _ (Jmp l) = sendSubR sub $ Jmp l

patchHeftyS :: forall h t a. (Patch h, Fresh < t, X86 << h, AlphaEffect h, Alpha a) => NameMap (Const AccessType) -> HeftyS h a -> TL t h a
patchHeftyS = go where
  go :: NameMap (Const AccessType) -> HeftyS h a -> TL t h a
  go _ (ReturnS x) = pure x
  go m (OpS op n k) = 
    patch id m op >>= \n' -> go (insertName n' (Const (getAccessType op)) m) (rename n n' k)

patchInstructions :: (Fresh < f, X86 << g, Patch g, AlphaEffect g) => TL f g (Name Val) -> TL f g (Name Val)
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

class HTraversable f => Pretty f where
  prettyOp :: Pretty g => NameMap (Const String) -> f (HeftyS g) (Name a) -> String -> String
  prettyVar :: f (HeftyS g) (Name a) -> String

instance (Pretty f, Pretty g) => Pretty (f ++ g) where
  prettyOp m (LH x) = prettyOp m x
  prettyOp m (RH x) = prettyOp m x
  prettyVar (LH x) = prettyVar x
  prettyVar (RH x) = prettyVar x

pOp :: String -> [String] -> String -> String
pOp op xs = (("\t" ++ op ++ " " ++ intercalate ", " xs ++ "\n") ++)

instance Pretty X86 where
  prettyOp m = \case
    Reg{} -> id
    Deref{} -> id
    Imm{} -> id
    Addq x y -> pOp "addq" [m ! x, m ! y]
    Subq x y -> pOp "subq" [m ! x, m ! y]
    Negq x -> pOp "negq" [m ! x]
    Movq x y -> pOp "movq" [m ! x, m ! y]
    Callq l -> pOp "callq" [getLabel l]
    Globl l -> ((".globl " ++ getLabel l ++ "\n") ++)
    Pushq x -> pOp "pushq" [m ! x]
    Popq x -> pOp "popq" [m ! x]
    Retq -> pOp "retq" []
    where
      m ! k = getConst $ lookupName k m
  prettyVar (Reg r) = prettyReg r
  prettyVar (Deref r i) = show i ++ "(" ++ prettyReg r ++ ")"
  prettyVar (Imm n) = "$" ++ show n
  prettyVar _ = "()"

instance Pretty X86Cond where
  prettyOp m = \case
    ByteReg{} -> id
    Xorq x y -> pOp "xorq" [m ! x, m ! y]
    Cmpq x y -> pOp "cmpq" [m ! x, m ! y]
    Setcc cc x -> pOp ("set" ++ prettyCC cc) [m ! x]
    Movzbq x y -> pOp "movzbq" [m ! x, m ! y]
    Jcc cc l -> pOp ("j" ++ prettyCC cc) [getLabel l]
    where
      m ! k = getConst $ lookupName k m
  prettyVar (ByteReg r) = prettyByteReg r
  prettyVar _ = "()"

instance Pretty Block where
  prettyOp m (Blocks bs) = foldr (\(L lbl, x) xs -> ((lbl ++ ":\n") ++) . prettyHeftyS m x . xs) id bs

  prettyOp _ (Jmp l) = pOp "jmp" [getLabel l]
  prettyVar _ = "()"

prettyHeftyS :: (Pretty h) => NameMap (Const String) -> HeftyS h a -> String -> String
prettyHeftyS = go where
  go _ ReturnS{} = id
  go m (OpS op n k) = prettyOp m op . go (insertName n (Const (prettyVar op)) m) k

prettyPrint :: (Pretty g) => TL f g (Name ()) -> TL f g' String
prettyPrint = fmap (($ "") . prettyHeftyS emptyNameMap) . flush

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
      program = denote $ LAdd (LInt 1) (LInt 2)
--         LLet LRead \x ->
--            LLet LRead \y ->
--              LIf
--                (LCmp Ge (LVar x) (LVar y))
--                (LSub (LVar x) (LVar y))
--                (LSub (LVar y) (LVar x))
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
      pretty = prettyPrint full
   in putStrLn $ nilTL (hFresh pretty)

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