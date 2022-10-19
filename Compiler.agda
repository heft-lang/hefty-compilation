{-# OPTIONS --overlapping-instances --instance-search-depth=10 #-}
module Compiler where

-- open import Agda.Builtin.FromNat
open import Data.Integer using ( ℤ )
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
open FreeModule hiding ( _>>=_ ; _>>_ )
open Effect
open Effectᴴ
open import Agda.Primitive
open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])
open ≡-Reasoning
open import Data.List hiding ( _++_ )
open import Data.Empty
open import Data.Maybe hiding ( _>>=_ )
open import Effect.Functor

open Alg

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

weakenᵣ : { F : Set → Set } ⦃ w : H ∼ H₀ ▹ H′ ⦄ → Alg H F → Alg H′ F
alg (weakenᵣ {F = F} α) op ψ k = alg α
  (inj▹ᵣ op)
  (subst (λ x → (s : Op x) → F (Ret x s)) (sym $ inj▹ᵣ-fork≡ op) ψ)
  (subst (λ x → x → F _) (sym $ inj▹ᵣ-ret≡ op) k)

-- Note: this has strict semantics
let-Alg : ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ ⦃ w₁ : H ∼ Let ▹ H′ ⦄ → Alg H (Hefty H′)
let-Alg = handle▹
  (mkAlg (λ { letop ψ k → ψ nothing >>= λ x → ψ (just x) >>= k } ))
  (mkAlg impure)

arith-Alg :
  { H⁗ : Effectᴴ } ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ ⦃ _ : HasLabel u ⦄
  ⦃ w₁ : H  ∼ Lift Arith  ▹ H″ ⦄
  ⦃ w₂ : H′ ∼ Lift X86Var ▹ H‴ ⦄
  ⦃ w₃ : H′ ∼ Lift X86  ▹ H⁗ ⦄
  ⦃ w₄ : H″ ⊂ H′ ⦄
  →
  Alg H (Hefty H′)
arith-Alg ⦃ w₂ = w₂ ⦄ = handle▹
  (mkAlg (λ {
    (add x y) _ k → (↑ x86var) >>= λ z → (↑ (movq x z)) >>= λ _ → (↑ (addq y z)) >>= λ _ → k z ;
    (sub x y) _ k → (↑ x86var) >>= λ z → (↑ (movq x z)) >>= λ _ → (↑ (subq y z)) >>= λ _ → k z ;
    (neg x  ) _ k → (↑ x86var) >>= λ z → (↑ (movq x z)) >>= λ _ → (↑ (negq z))   >>= λ _ → k z
  }))
  weaken

read-Alg :
  { H⁗ : Effectᴴ } ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ ⦃ _ : HasLabel u ⦄
  ⦃ w₁ : H  ∼ Lift Read   ▹ H″ ⦄
  ⦃ w₂ : H′ ∼ Lift X86Var ▹ H‴ ⦄
  ⦃ w₃ : H′ ∼ Lift X86  ▹ H⁗ ⦄
  ⦃ w₄ : H″ ⊂ H′ ⦄
  →
  ⟦ lab ⟧ → Alg H (Hefty H′)
read-Alg ⦃ w₂ = w₂ ⦄ read-int-lab = handle▹
  (mkAlg (λ {
    read _ k → (↑ x86var) >>= λ z → (↑ (callq read-int-lab)) >>= λ _ → (↑ (reg Rax)) >>= λ x → (↑ (movq x z)) >>= λ _ → k z
  }))
  weaken

-- Hefty H (F x) → F (Hefty H x)

module CountVars where
  open Universe ⦃ ... ⦄

  private
    instance
      UnitUniverse : Universe
      Universe.T UnitUniverse = ⊤
      Universe.⟦ UnitUniverse ⟧ tt = ⊤

  private
    instance
      UnitHasVal : HasVal UnitUniverse
      HasVal.val UnitHasVal = tt

  countVars-Alg :
    ⦃ H ∼ Lift X86Var ▹ H′ ⦄ →
    Alg H (λ _ → ℕ)
  countVars-Alg =
    handle▹ (mkAlg λ { x86var _ k → 1 + k tt }) ({!!})
open CountVars using (countVars-Alg)

module TraverseModule where
  open RawFunctor ⦃ ... ⦄

  data Env : Set where

  NatUniverse : Universe
  Universe.T NatUniverse = ⊤
  Universe.⟦ NatUniverse ⟧ tt = ℕ

  private
    instance
      NatHasVal : HasVal NatUniverse
      HasVal.val NatHasVal = tt

  private
    instance
      NatHasLab : HasLabel NatUniverse
      HasLabel.lab NatHasLab = tt

  record Traverse (H : (u : Universe) → ⦃ _ : HasVal u ⦄ ⦃ _ : HasLabel u ⦄ → Effectᴴ) : Set₁ where
    field
      traverse : ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ ⦃ _ : HasLabel u ⦄ → Alg (H NatUniverse) (λ x → Env → Hefty (H u) x)
  open Traverse ⦃ ... ⦄

  insertEnv : {A : Set} → A → Env → ℕ × Env
  insertEnv = {!!}

  private
    instance
      LiftTraverse : Traverse (λ u → Lift (Imm ⦃ u ⦄))
      Traverse.traverse LiftTraverse =
        mkAlg λ { (imm n) ψ k env → impure (imm n) (λ x → ⊥-elim x) λ x → let (x' , env') = insertEnv x env in k x' env' }

-- TODO:
--  [x] Weaken let2set_Alg
--  [x] Change let to have two higher-order arguments
--  [x] Split out common structure of let2set_Alg
--  [x] Uniquify variables
--  [x] X86Var
--  [ ] Stack allocation → X86
--  [ ] More types than just ℤ (Intrinsically typed AST?)
--  [ ] Bigger language (e.g. if statement)
--  [ ] Correctness proofs

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
  {H₅ : Effectᴴ}
  ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ ⦃ _ : HasLabel u ⦄
  ⦃ w₁ : H ∼ Lift X86Var ▹ H₁ ⦄
  ⦃ w₂ : H ∼ Lift X86  ▹ H₂ ⦄
  ⦃ w₄ : H ∼ Lift Read ▹ H₄ ⦄
  ⦃ w₅ : H ∼ Lift Imm ▹ H₅ ⦄
  →
  Hefty H ⟦ val ⟧
ex0-3 {H = H} = cataᴴ pure arith-Alg (ex0-2 {Lift Arith ∔ H})

ex0-4 :
  {H₅ : Effectᴴ}
  ⦃ u : Universe ⦄ ⦃ _ : HasVal u ⦄ ⦃ _ : HasLabel u ⦄
  ⦃ w₁ : H ∼ Lift X86Var ▹ H₁ ⦄
  ⦃ w₂ : H ∼ Lift X86  ▹ H₂ ⦄
  ⦃ w₄ : H ∼ Lift Imm ▹ H₄ ⦄
  →
  ⟦ lab ⟧ → Hefty H ⟦ val ⟧
ex0-4 {H = H} read-int-lab = cataᴴ pure (read-Alg read-int-lab) (ex0-3 {Lift Read ∔ H})

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
