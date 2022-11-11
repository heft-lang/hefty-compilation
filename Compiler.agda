{-# OPTIONS --overlapping-instances --instance-search-depth=10 #-}
module Compiler where

open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg
open import Data.Integer using ( ℤ ; _*_  ; +_ ; -_ )
import Data.Integer as ℤ
import Data.Integer.Show as ℤShow
open import Data.Nat using (ℕ ; _+_ ; suc)
open import Data.Nat.Show using ( show )
open import Data.String using (String ; _==_ ; _++_ )
open import Data.Unit
open import Data.Bool hiding ( T )
open import Data.Product
open import Function
open import Hefty
open HeftyModule
open import Algebraic
open FreeModule hiding ( _>>=_ ; _>>_ ; pure )
open Effect
open Effectᴴ
open import Agda.Primitive
open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])
open ≡-Reasoning
open import Data.List hiding ( _++_ )
open import Data.Empty
open import Data.Maybe hiding ( _>>=_ )
open import Effect.Functor
open import Effect.Applicative
open import Data.Sum

open Alg

instance
  Numℕ : Number ℕ
  Numℕ .Number.Constraint _ = ⊤
  Numℕ .Number.fromNat    m = m

instance
  Numℤ : Number ℤ
  Numℤ .Number.Constraint _ = ⊤
  Numℤ .Number.fromNat    m = + m

data Reg : Set where
  Rsp Rbp Rax Rbx Rcx Rdx Rsi Rdi : Reg
open Reg

Label = String

record _⊂_ (H : Effectᴴ) (H′ : Effectᴴ) : Set₁ where
  field
    weaken : Alg H (Hefty H′)
open _⊂_ ⦃ ... ⦄

instance
  Refl⊂ : H ⊂ H
  _⊂_.weaken Refl⊂ = mkAlg impure

Left⊂ : H ⊂ (H ∔ H₂)
alg (_⊂_.weaken Left⊂) op ψ k = impure (inj₁ op) ψ k

Right⊂ : H ⊂ (H₁ ∔ H)
alg (_⊂_.weaken Right⊂) op ψ k = impure (inj₂ op) ψ k

open Universe ⦃ ... ⦄

record HasVal (u : Universe) : Set where
  field
    val : Universe.T u
open HasVal ⦃ ... ⦄

record HasLabel (u : Universe) : Set where
  field
    lab : Universe.T u
open HasLabel ⦃ ... ⦄

module Effects where

  variable
    A : Set

  -- Imm(ediate)

  data ImmOp : Set where
    imm : ℤ → ImmOp

  Imm : ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ → Effect
  Op Imm = ImmOp
  Ret Imm (imm _) = ⟦ val ⟧

  -- Arith(methic)

  data ArithOp ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ : Set where
    neg : ⟦ val ⟧ → ArithOp
    add : ⟦ val ⟧ → ⟦ val ⟧ → ArithOp
    sub : ⟦ val ⟧ → ⟦ val ⟧ → ArithOp

  Arith : ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ → Effect
  Op Arith = ArithOp
  Ret Arith (neg x)   = ⟦ val ⟧
  Ret Arith (add x y) = ⟦ val ⟧
  Ret Arith (sub x y) = ⟦ val ⟧

  -- Read

  data ReadOp : Set where
    read : ReadOp

  Read : ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ → Effect
  Op Read = ReadOp
  Ret Read read  = ⟦ val ⟧

  -- Let (non recursive)

  data LetOp : Set where
    letop : LetOp

  Let : ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ → Effectᴴ
  Op Let = LetOp
  Op (Fork Let letop) = Maybe ⟦ val ⟧
  Ret (Fork Let letop) _ = ⟦ val ⟧
  Ret Let letop = ⟦ val ⟧

  ‵let : ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ ⦃ w : H ∼ Let ▹ H′ ⦄
       → Hefty H ⟦ val ⟧ → (⟦ val ⟧ → Hefty H ⟦ val ⟧) → Hefty H ⟦ val ⟧
  ‵let ⦃ w = w ⦄ m₁ m₂ =
    impure
      (inj▹ₗ letop)
      (proj-fork▹ₗ ⦃ w ⦄ (λ { nothing → m₁; (just x) → m₂ x }))
      (pure ∘ proj-ret▹ₗ ⦃ w ⦄)

  -- X86Var

  data X86VarOp : Set where
    x86var : X86VarOp

  X86Var : ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ → Effect
  Op X86Var = X86VarOp
  Ret X86Var x86var = ⟦ val ⟧

  -- X86

  data X86Op ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ ⦃ _ : HasLabel u ⦄ : Set where
    reg : Reg → X86Op
    deref : Reg → ℤ → X86Op
    addq : ⟦ val ⟧ → ⟦ val ⟧ → X86Op
    subq : ⟦ val ⟧ → ⟦ val ⟧ → X86Op
    negq : ⟦ val ⟧ → X86Op
    movq : ⟦ val ⟧ → ⟦ val ⟧ → X86Op
    pushq : ⟦ val ⟧ → X86Op
    popq : ⟦ val ⟧ → X86Op
    callq : ⟦ lab ⟧ → X86Op
    retq : X86Op
    jmp : ⟦ lab ⟧ → X86Op
    label : X86Op

  X86 : ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ ⦃ _ : HasLabel u ⦄ → Effect
  Op X86 = X86Op
  Ret X86 (reg _) = ⟦ val ⟧
  Ret X86 (deref _ _) = ⟦ val ⟧
  Ret X86 (addq _ _) = ⊤
  Ret X86 (subq _ _) = ⊤
  Ret X86 (negq _) = ⊤
  Ret X86 (movq _ _) = ⊤
  Ret X86 (pushq _) = ⊤
  Ret X86 (popq _) = ⊤
  Ret X86 (callq _) = ⊤
  Ret X86 retq = ⊤
  Ret X86 (jmp _) = ⊤
  Ret X86 label = ⟦ lab ⟧

open Effects

data LExp ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ : Set where
  LInt  : ℤ → LExp
  LRead : LExp
  LNeg  : LExp → LExp
  LAdd  : LExp → LExp → LExp
  LSub  : LExp → LExp → LExp
  LVar  : ⟦ val ⟧ → LExp
  -- Note: this is a non recursive let
  LLet  : LExp → (⟦ val ⟧ → LExp) → LExp

⟦_⟧e :
  ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄
  ⦃ w₁ : H ∼ Lift Arith ▹ H₁ ⦄
  ⦃ w₂ : H ∼ Lift Read ▹ H₂ ⦄
  ⦃ w₃ : H ∼ Let ▹ H₃ ⦄
  ⦃ w₄ : H ∼ Lift Imm ▹ H₄ ⦄
  →
  LExp → Hefty H ⟦ val ⟧
⟦ LInt n ⟧e = ↑ (imm n)
⟦ LRead ⟧e = ↑ read
⟦ LNeg x ⟧e = ⟦ x ⟧e >>= λ x → ↑ (neg x)
⟦ LAdd x y ⟧e = ⟦ x ⟧e >>= λ x → ⟦ y ⟧e >>= λ y → ↑ (add x y)
⟦ LSub x y ⟧e = ⟦ x ⟧e >>= λ x → ⟦ y ⟧e >>= λ y → ↑ (sub x y)
⟦ LVar v ⟧e = pure v
⟦ LLet x f ⟧e = ‵let ⟦ x ⟧e (λ y → ⟦ f y ⟧e)

-- Note: this has strict semantics
let-Alg : ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ ⦃ w₁ : H ∼ Let ▹ H′ ⦄ → Alg H (Hefty H′)
let-Alg = handle▹
  (mkAlg λ { letop ψ k → ψ nothing >>= λ x → ψ (just x) >>= k })
  weaken

arith-Alg :
  { H⁗ : Effectᴴ } ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ ⦃ _ : HasLabel u ⦄
  ⦃ w₁ : H  ∼ Lift Arith  ▹ H″ ⦄
  ⦃ w₂ : H′ ∼ Lift X86Var ▹ H‴ ⦄
  ⦃ w₃ : H′ ∼ Lift X86    ▹ H⁗ ⦄
  ⦃ w₄ : H″ ⊂ H′ ⦄
  →
  Alg H (Hefty H′)
arith-Alg ⦃ w₂ = w₂ ⦄ = handle▹
  (mkAlg λ {
    (add x y) _ k → (↑ x86var) >>= λ z → (↑ movq x z) >>= λ _ → (↑ addq y z) >>= λ _ → k z ;
    (sub x y) _ k → (↑ x86var) >>= λ z → (↑ movq x z) >>= λ _ → (↑ subq y z) >>= λ _ → k z ;
    (neg x  ) _ k → (↑ x86var) >>= λ z → (↑ movq x z) >>= λ _ → (↑ negq z)   >>= λ _ → k z
  })
  weaken

read-Alg :
  { H⁗ : Effectᴴ } ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ ⦃ _ : HasLabel u ⦄
  ⦃ w₁ : H  ∼ Lift Read   ▹ H″ ⦄
  ⦃ w₂ : H′ ∼ Lift X86Var ▹ H‴ ⦄
  ⦃ w₃ : H′ ∼ Lift X86    ▹ H⁗ ⦄
  ⦃ w₄ : H″ ⊂ H′ ⦄
  →
  ⟦ lab ⟧ → Alg H (Hefty H′)
read-Alg ⦃ w₂ = w₂ ⦄ read-int-lab = handle▹
  (mkAlg λ {
    read _ k → (↑ x86var) >>= λ z → (↑ callq read-int-lab) >>= λ _ → (↑ reg Rax) >>= λ x → (↑ movq x z) >>= λ _ → k z
  })
  weaken

countVars : ({op : Op (Lift ε)} → Ret ε op) → Alg (Lift ε) (const ℕ)
alg (countVars def) op _ k = 1 + k def

x86var-Alg : ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ ⦃ _ : HasLabel u ⦄
  ⦃ w₁ : H ∼ Lift X86Var ▹ H′ ⦄
  ⦃ w₂ : H′ ∼ Lift X86 ▹ H″ ⦄
  →
  Alg H (λ x → ℕ → Hefty H′ x)
x86var-Alg = handle▹
  (mkAlg λ { x86var _ k n → (↑ (deref Rbp ((- 8) * fromNat n))) >>= λ z → k z (n + 1) })
  (mkAlg λ op ψ k n → impure op (λ x → ψ x 1) (λ x → k x n))

module StringUniverse where

  StringUniverse : Universe
  Universe.T StringUniverse = ⊤
  Universe.⟦ StringUniverse ⟧ tt = String

  private instance
    MyStringUniverse : Universe
    MyStringUniverse = StringUniverse

  instance
    StringHasVal : HasVal StringUniverse
    HasVal.val StringHasVal = tt

  instance
    StringHasLab : HasLabel StringUniverse
    HasLabel.lab StringHasLab = tt

  pretty-imm : Alg (Lift Imm) (λ _ → String)
  pretty-imm = mkAlg λ { (imm n) _ k → k (ℤShow.show n) }

  showReg : Reg → String
  showReg Rax = "%rax"
  showReg Rsp = "%rsp"
  showReg Rbp = "%rbp"
  showReg Rbx = "%rbx"
  showReg Rcx = "%rcx"
  showReg Rdx = "%rdx"
  showReg Rdi = "%rdi"
  showReg Rsi = "%rsi"

  pretty-x86 : Alg (Lift X86) (λ _ → String)
  pretty-x86 = mkAlg λ
    { (reg r) _ k → k (showReg r)
    ; (deref r i) _ k → k (ℤShow.show i ++ "(" ++ showReg r ++ ")")
    ; (addq x y) _ k → "addq " ++ x ++ ", " ++ y ++ "\n" ++ k tt
    ; (subq x y) _ k → "subq " ++ x ++ ", " ++ y ++ "\n" ++ k tt
    ; (negq x) _ k → "negq " ++ x ++ "\n" ++ k tt
    ; (movq x y) _ k → "movq " ++ x ++ ", " ++ y ++ "\n" ++ k tt 
    ; (pushq x) _ k → "pushq " ++ x ++ "\n" ++ k tt 
    ; (popq x) _ k → "popq " ++ x ++ "\n" ++ k tt 
    ; (callq l) _ k → "callq " ++ l ++ "\n" ++ k tt 
    ; retq _ k → "retq\n" ++ k tt
    ; (jmp l) _ k → "jmp " ++ l ++ "\n" ++ k tt
    ; label _ k → k "somelabel" -- TODO: generate unique labels
    }

open StringUniverse

nil-Alg : {F : Set → Set} → Alg (Lift Nil) F
nil-Alg = mkAlg λ x _ _ → ⊥-elim x

ex0-0 : ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ → LExp
ex0-0 = LLet LRead (λ x → LAdd (LVar x) (LVar x))

ex0-1 :
  ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄
  ⦃ w₁ : H ∼ Lift Arith ▹ H₁ ⦄
  ⦃ w₂ : H ∼ Lift Read ▹ H₂ ⦄
  ⦃ w₃ : H ∼ Let ▹ H₃ ⦄
  ⦃ w₄ : H ∼ Lift Imm ▹ H₄ ⦄
  →
  Hefty H ⟦ val ⟧
ex0-1 = ⟦ ex0-0 ⟧e

ex0-2 :
  ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄
  ⦃ w₁ : H ∼ Lift Arith ▹ H₁ ⦄
  ⦃ w₂ : H ∼ Lift Read ▹ H₂ ⦄
  ⦃ w₃ : H ∼ Lift Imm ▹ H₃ ⦄
  →
  Hefty H ⟦ val ⟧
ex0-2 = cataᴴ pure let-Alg ex0-1

ex0-3 :
  ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ ⦃ _ : HasLabel u ⦄
  ⦃ w₁ : H ∼ Lift X86Var ▹ H₁ ⦄
  ⦃ w₂ : H ∼ Lift X86 ▹ H₂ ⦄
  ⦃ w₃ : H ∼ Lift Read ▹ H₃ ⦄
  ⦃ w₄ : H ∼ Lift Imm ▹ H₄ ⦄
  →
  Hefty H ⟦ val ⟧
ex0-3 {H = H} = cataᴴ pure arith-Alg (ex0-2 {Lift Arith ∔ H})

ex0-4 :
  ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ ⦃ _ : HasLabel u ⦄
  ⦃ w₁ : H ∼ Lift X86Var ▹ H₁ ⦄
  ⦃ w₂ : H ∼ Lift X86 ▹ H₂ ⦄
  ⦃ w₃ : H ∼ Lift Imm ▹ H₃ ⦄
  →
  ⟦ lab ⟧ → Hefty H ⟦ val ⟧
ex0-4 {H = H} read-int-lab = cataᴴ pure (read-Alg read-int-lab) (ex0-3 {Lift Read ∔ H})

ex0-5 :
  ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ ⦃ _ : HasLabel u ⦄
  ⦃ w₂ : H ∼ Lift X86 ▹ H₂ ⦄
  ⦃ w₃ : H ∼ Lift Imm ▹ H₃ ⦄
  →
  ⟦ lab ⟧ → Hefty H ⟦ val ⟧
ex0-5 {H = H} read-int-lab = cataᴴ (λ x _ → pure x) x86var-Alg (ex0-4 read-int-lab) 1

ex0-6 : String
ex0-6 = cataᴴ (const "") (pretty-imm ⋎ pretty-x86 ⋎ nil-Alg) (ex0-5 ⦃ StringUniverse ⦄ "_read_int")

-- TODO:
--  [x] Weaken let2set_Alg
--  [x] Change let to have two higher-order arguments
--  [x] Split out common structure of let2set_Alg
--  [x] Uniquify variables
--  [x] X86Var
--  [x] Stack allocation → X86
--  [ ] More types than just ℤ (Intrinsically typed AST?)
--  [ ] Bigger language (e.g. if statement)
--  [ ] Correctness proofs

-- instance
--   Negativeℤ : Negative ℤ
--   Negativeℤ = ℤ.Negative

-- mapHefty : ∀ {A B} → (A → B) → Hefty H A → Hefty H B
-- mapHefty f (return x) = return (f x)
-- mapHefty f (impure op ψ k) = impure op ψ (λ x → mapHefty f (k x))
--
-- instance
--   HeftyFunctor : RawFunctor (Hefty H)
--   HeftyFunctor = record {_<$>_ = mapHefty}
--
-- apHefty : ∀ {A B} → Hefty H (A → B) → Hefty H A → Hefty H B
-- apHefty (return f) h = mapHefty f h
-- apHefty (impure op ψ k) h = impure op ψ (λ x → apHefty (k x) h)
--
-- instance
--   HeftyApplicative : RawApplicative (Hefty H)
--   HeftyApplicative = record
--     { pure = return
--     ; _⊛_ = apHefty
--     }
--
-- bindHefty : ∀ {A B} → Hefty H A → (A → Hefty H B) → Hefty H B
-- bindHefty (return x) f = f x
-- bindHefty (impure op ψ k) f = impure op ψ (λ x → bindHefty (k x) f)
--
-- instance
--   HeftyMonad : RawMonad (Hefty H)
--   HeftyMonad = record
--     { _>>=_ = bindHefty
--     ; return = return
--     }


-- module CountVars where
--   open Universe ⦃ ... ⦄
--
--   private
--     instance
--       UnitUniverse : Universe
--       Universe.T UnitUniverse = ⊤
--       Universe.⟦ UnitUniverse ⟧ tt = ⊤
--
--   private
--     instance
--       UnitHasVal : HasVal UnitUniverse
--       HasVal.val UnitHasVal = tt
--
--   countVars-Alg :
--     ⦃ H ∼ Lift X86Var ▹ H′ ⦄ →
--     Alg H (λ _ → ℕ)
--   countVars-Alg =
--     handle▹ (mkAlg λ { x86var _ k → 1 + k tt }) ({!!})
-- open CountVars using (countVars-Alg)

-- module NatUniverse where
--   -- open RawFunctor ⦃ ... ⦄
--
--   NatUniverse : Universe
--   Universe.T NatUniverse = ⊤
--   Universe.⟦ NatUniverse ⟧ tt = ℕ
--
--   instance
--       NatHasVal : HasVal NatUniverse
--       HasVal.val NatHasVal = tt
--
--   instance
--       NatHasLab : HasLabel NatUniverse
--       HasLabel.lab NatHasLab = tt

--   record Sequence (H : (u : Universe) → ⦃ _ : HasVal u ⦄ ⦃ _ : HasLabel u ⦄ → Effectᴴ) : Set₁ where
--     field
--       sequence : ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ ⦃ _ : HasLabel u ⦄ { H′ : (u : Universe) → ⦃ _ : HasVal u ⦄ ⦃ _ : HasLabel u ⦄ → Effectᴴ} ⦃ sub : H u ⊂ H′ u ⦄ → Alg (H NatUniverse) (λ x → Env → Hefty (H′ u) x)
--   open Sequence ⦃ ... ⦄
--
--
--   instance
--     ImmSequence : Sequence (λ u → Lift (Imm ⦃ u ⦄))
--     alg (Sequence.sequence ImmSequence) =
--       λ { (imm n) ψ k env → (cataᴴ pure weaken (impure (imm n) (λ x → ⊥-elim x) pure)) >>= λ x → let (x' , env') = insertEnv env x in k x' env' }
--
--   instance
--     ArithSequence : Sequence (λ u → Lift (Arith ⦃ u ⦄))
--     alg (Sequence.sequence ArithSequence) =
--       λ { (add x y) ψ k env → let x' = lookupEnv env x ; y' = lookupEnv env y in cataᴴ pure weaken (impure (add x' y') (λ x → ⊥-elim x) pure) >>= λ x → let (x' , env') = insertEnv env x in k x' env'
--         ; (sub x y) ψ k env → let x' = lookupEnv env x ; y' = lookupEnv env y in cataᴴ pure weaken (impure (sub x' y') (λ x → ⊥-elim x) pure) >>= λ x → let (x' , env') = insertEnv env x in k x' env'
--         ; (neg x)   ψ k env → let x' = lookupEnv env x                        in cataᴴ pure weaken (impure (neg x')    (λ x → ⊥-elim x) pure) >>= λ x → let (x' , env') = insertEnv env x in k x' env'
--         }
--
--   -- TODO the rest of the effects
--
--   lsub : (H₁ ∔ H₂) ⊂ H′ → H₁ ⊂ H′
--   alg (_⊂_.weaken (lsub x)) = alg (weaken ⦃ x ⦄) ∘ inj₁
--
--   rsub : (H₁ ∔ H₂) ⊂ H′ → H₂ ⊂ H′
--   alg (_⊂_.weaken (rsub x)) = alg (weaken ⦃ x ⦄) ∘ inj₂
--
--   instance
--     SumSequence : { H₁ H₂ : ⦃ u : Universe ⦄ → Effectᴴ } ⦃ s₁ : Sequence (λ u → H₁ ⦃ u ⦄) ⦄ ⦃ s₂ : Sequence (λ u → H₂ ⦃ u ⦄) ⦄ → Sequence (λ u → H₁ ⦃ u ⦄ ∔ H₂ ⦃ u ⦄)
--     alg (Sequence.sequence (SumSequence ⦃ s₁ = s₁ ⦄ ⦃ s₂ = s₂ ⦄ ) {H′ = H′} ⦃ sub = sub₁ ⦄) =
--       λ { (inj₁ op) ψ k → alg (sequence {H′ = H′} ⦃ sub = lsub sub₁ ⦄) op ψ k
--         ; (inj₂ op) ψ k → alg (sequence {H′ = H′} ⦃ sub = rsub sub₁ ⦄) op ψ k
--         }

-- -- Kleisli arrow in the category of higher-order effect morphisms?
-- record Pass (M : Set → Set) (H : Effectᴴ) (H′ : Effectᴴ) : Set₁ where
--   constructor mkPass
--   field pass :  (op  : Op H)
--                 (ψ   : (s : Op (Fork H op)) → Hefty H′ (Ret (Fork H op) s))
--                 (k   : Ret H op → Hefty H′ A)
--             → M (Hefty H′ A)
-- open Pass
--
-- _>>=ₘ_ : { M : Set → Set } ⦃ _ : RawMonad M ⦄ → ∀ {A B} → M A → (A → M B) → M B
-- _>>=ₘ_ ⦃ m ⦄ = RawMonad._>>=_ m
--
-- -- Here's what will need to change:
-- --
-- --  * M should additionally always contain a way to store ℕ ↔ A bindings and retrieve them
-- --    This should be discharged upon `cataPass`
-- --
-- --  This won't work because the value we need to store is only available from a function within M
-- --  we cannot run something like `store : A → ℤ → M ⊤` to store it for later use.
--
-- data Env : Set where
--
-- postulate insertEnv : {A : Set} → Env → A → ℕ → Env
-- postulate lookupEnv : {A : Set} → Env → ℕ → A
-- postulate freshEnv : Env → ℕ
-- postulate emptyEnv : Env
--
-- cataPass :
--   { M : Set → Set }
--   ⦃ _ : RawMonad M ⦄ →
--
--   Env →
--
--   ({op : Op H} → ((s : Op (Fork H op)) → M (Hefty H′ (Ret (Fork H op) s))) →
--     M ((s : Op (Fork H op)) → Hefty H′ (Ret (Fork H op) s))) →
--
--   (Env → {op : Op H} → ∀ {A} → (Env → Ret H op → M (Hefty H′ A)) →
--     M (Ret H op → Hefty H′ A)) →
--
--   (∀ {A} → A → M (Hefty H′ A)) →
--   Pass M H H′ → Hefty H A → M (Hefty H′ A)
--
-- cataPass env _ _ g _ (return x) = g x
-- cataPass env sequenceFork sequenceK g p (impure op ψ k) =
--   sequenceFork (λ x → cataPass env sequenceFork sequenceK g p (ψ x)) >>=ₘ λ ψ′ →
--   sequenceK env (λ env′ x → cataPass env′ sequenceFork sequenceK g p (k x)) >>=ₘ λ k′ →
--   pass p op ψ′ k′
--
-- sequenceForkLift : ⦃ u : Universe ⦄ { M : Set → Set } ⦃ m : RawMonad M ⦄ {op : Op (Lift ε)} → ((s : Op (Fork (Lift ε) op)) → M (Hefty H′ (Ret (Fork (Lift ε) op) s))) → M ((s : Op (Fork (Lift ε) op)) → Hefty H′ (Ret (Fork (Lift ε) op) s))
-- sequenceForkLift ⦃ m = m ⦄ f = pure (λ x → ⊥-elim x)
--
-- -- postulate store : A → M ℤ
-- -- postulate retrieve : ℤ → M A
--
-- sequenceKArith :
--   ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄
--   { M : Set → Set } ⦃ m : RawMonad M ⦄ →
--   Env →
--   {op : {u : Universe} ⦃ _ : HasVal u ⦄ → Op (Lift (Arith ⦃ u ⦄))} →
--   ∀ {A} →
--   (Env → Ret (Lift (Arith ⦃ NatUniverse.NatUniverse ⦄)) op → M (Hefty H′ A)) →
--   M (Ret (Lift (Arith ⦃ u ⦄))  op → Hefty H′ A)
-- sequenceKArith env {op = op} f with freshEnv env
-- ... | n with op {NatUniverse.NatUniverse}
-- ...     | neg x = {!!} <$> f {!!} {!!}
-- ...     | add x y = {!!}
-- ...     | sub x y = {!!}
-- gensym : List String → String → String
-- gensym xs x with length (filterᵇ (x ==_) xs)
-- ... | 0 = x
-- ... | n = x ++ show n

-- Only uniquifies variables that occur in the same scope (i.e. those that would be shadowed)
-- assumes non recursive let
-- uniquify_Alg :
--   ⦃ w₁ : H ∼ (Let A) ▹ H′ ⦄ ⦃ w₂ : H′ ∼ Lift (Var A) ▹ H″ ⦄ ⦃ w₃ : H ∼ Lift (Var A) ▹ H‴ ⦄ →
--   Alg H (λ x → List String → Hefty H x)
-- uniquify_Alg ⦃ w₁ ⦄ ⦃ w₂ ⦄ ⦃ w₃ ⦄ =
--   handle▹ ⦃ w₁ ⦄
--     (mkAlg λ { (letop v) ψ k env → ‵let (gensym env v) (ψ false env) (ψ true (v ∷ env)) >>= λ x → k x env })
--     (handle▹ ⦃ w₂ ⦄
--       (mkAlg λ { (var v) _ k env → (↑_ ⦃ w₃ ⦄ (var (gensym env v))) >>= λ x → k x env })
--       (weakenᵣ ⦃ w₂ ⦄ (weakenᵣ ⦃ w₁ ⦄ (mkAlg λ op ψ k env → impure op (λ x → ψ x env) (λ x → k x env)))))

--     field alg  :  (op  : Op H)
--                   (ψ   : (s : Op (Fork H op)) → G (Ret (Fork H op) s))
--                   (k   : Ret H op → G A)
--                →  G A

-- globalUniquify_Alg :
--   ⦃ w₁ : H ∼ (Let A) ▹ H′ ⦄ ⦃ w₂ : H′ ∼ Lift (Var A) ▹ H″ ⦄ ⦃ w₃ : H ∼ Lift (Var A) ▹ H‴ ⦄ →
-- --   ({A : Set} (M : Set → Set) → Hefty H (M A) → M (Hefty H A)) →
-- --   ((op : Op H) (M : Set → Set) → ((s : Op (Fork H op)) → Hefty H (M (Ret (Fork H op) s))) → M ((s : Op (Fork H op)) → Hefty H (Ret (Fork H op) s))) →
--   Alg H (λ x → List (String × ℕ) → ℕ → (Hefty H x × ℕ))
-- globalUniquify_Alg ⦃ w₁ ⦄ ⦃ w₂ ⦄ ⦃ w₃ ⦄ = -- sequence1 sequence2 =
--   handle▹ ⦃ w₁ ⦄
--     (mkAlg λ { (letop v) ψ k env s0 →
--       let env' = (v , s0) ∷ env in
--       let (x , s1) = (ψ false env (suc s0)) in
--       let (y , s2) = (ψ true env' s1) in
--       (‵let (v ++ "." ++ show s0) x y >>= λ x → proj₁ (k x env' s2)) , s2
--     })
--     (handle▹ ⦃ w₂ ⦄
--       (mkAlg λ { (var v) _ k env s0 → ((↑_ ⦃ w₃ ⦄ (var (v ++ "." ++ lookupOr env v show "unkown"))) >>= λ x → {!!}) , s0 })
--       (weakenᵣ ⦃ w₂ ⦄ (weakenᵣ ⦃ w₁ ⦄ (mkAlg λ op ψ k env s0 →
--         let (ψ′ , s1) = ψ {!!} env s0 in
--         (impure op {!!} (λ x → {!!})) , {!!} ))))


-- data Atom : Set where
--   AInt : ℤ → Atom
--   AVar : String → Atom
--
-- data CExp : Set where
--   CAtom : Atom → CExp
--   CRead : CExp
--   CNeg  : Atom → CExp
--   CAdd  : Atom → Atom → CExp
--   CSub  : Atom → Atom → CExp
--
-- data Stmt : Set where
--   Assign : String → CExp → Stmt
--
-- data CVar : Set where
--   Seq : Stmt → CVar → CVar
--   Return : CExp → CVar
