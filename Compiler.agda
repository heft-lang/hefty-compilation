module Compiler where

open import Data.Integer using ( ℤ ; _-_ ; -_ ; _+_ )
open import Data.String using ( String )
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
open import Data.List

module Effects where
  open Universe ⦃ ... ⦄

  variable
    A : Set

  data ReadOp : Set where
    read : ReadOp

  Read : Effect
  Op   Read       = ReadOp
  Ret  Read read  = ℤ

  ‵read : ⦃ ε ∼ Read ▸ ε′ ⦄ → Free ε ℤ
  ‵read ⦃ w ⦄ = impure (inj▸ₗ read) (pure ∘ proj-ret▸ₗ ⦃ w ⦄)

  data VarOp : Set where
    var : String → VarOp

  Var : Set → Effect
  Op (Var T) = VarOp
  Ret (Var T) (var _) = T

  ‵askvar : ⦃ w : ε ∼ Var A ▸ ε′ ⦄ → String → Free ε A
  ‵askvar ⦃ w ⦄ v = impure (inj▸ₗ (var v)) (pure ∘ proj-ret▸ₗ ⦃ w ⦄)

  data LetOp (T : Set) : Set where
    letvar : { T } → String → LetOp T

  Let : ⦃ u : Universe ⦄ → Set → Effectᴴ
  Op     (Let _) = LetOp T
  Fork   (Let A) (letvar {t} _)  = record
    { Op = Bool; Ret = λ { false → A; true → ⟦ t ⟧ } }
  Ret    (Let _) (letvar {t} _)  = ⟦ t ⟧

  ‵letvar   : ⦃ u : Universe ⦄ ⦃ w : H ∼ (Let A) ▹ H′ ⦄ {t : T}
           → String → Hefty H A → Hefty H ⟦ t ⟧ → Hefty H ⟦ t ⟧
  ‵letvar ⦃ w = w ⦄ v m₁ m₂ =
    impure
      (inj▹ₗ (letvar v))
      (proj-fork▹ₗ ⦃ w ⦄ (λ { false → m₁; true → m₂ }))
      (pure ∘ proj-ret▹ₗ ⦃ w ⦄)

  data SetVarOp (A : Set) : Set where
    -- getvar : String → SetVarOp A
    setvar : String → A → SetVarOp A

  SetVar : Set → Effect
  Op (SetVar A) = SetVarOp A
  -- Ret (SetVar A) (getvar _) = A
  Ret (SetVar A) (setvar _ _) = ⊤

  ‵setvar : ⦃ ε ∼ SetVar A ▸ ε′ ⦄ → String → A → Free ε ⊤
  ‵setvar ⦃ w ⦄ v x = impure (inj▸ₗ (setvar v x)) (pure ∘ proj-ret▸ₗ ⦃ w ⦄)

private
  data Type : Set where
    unit  : Type
    num   : Type

private instance
  TypeUniverse : Universe
  Universe.T TypeUniverse = Type
  Universe.⟦ TypeUniverse ⟧ unit  = ⊤
  Universe.⟦ TypeUniverse ⟧ num   = ℤ

open Effects

data LExp : Set where
  LInt  : ℤ → LExp
  LRead : LExp
  LNeg  : LExp → LExp
  LAdd  : LExp → LExp → LExp
  LSub  : LExp → LExp → LExp
  LVar  : String → LExp
  LLet  : String → LExp → LExp → LExp

-- variable
--   H H′ H″ : Effectᴴ

data Env : Set where

⟦_⟧ : ⦃ wᵣ : H ∼ Lift Read ▹ H′ ⦄ ⦃ wₜ : H ∼ (Let ℤ) ▹ H″ ⦄ ⦃ wₐ : H ∼ Lift (Var ℤ) ▹ H‴ ⦄ → LExp → Hefty H ℤ
⟦ LInt n ⟧ = pure n
⟦ LRead ⟧ = ↑ read
⟦ LNeg x ⟧ = ⟦ x ⟧ >>= λ x → pure (- x)
⟦ LAdd x y ⟧ = ⟦ x ⟧ >>= λ x → ⟦ y ⟧ >>= λ y → pure (x + y)
⟦ LSub x y ⟧ = ⟦ x ⟧ >>= λ x → ⟦ y ⟧ >>= λ y → pure (x - y)
⟦ LVar v ⟧ =  ↑ (var v)
⟦ LLet v x y ⟧ =  ‵letvar v ⟦ x ⟧ ⟦ y ⟧

open Alg

-- uniquify_Alg : ⦃ w₁ : H ∼ (Let A) ▹ H′ ⦄ ⦃ w₂ : H ∼ Lift (Var A) ▹ H″ ⦄ → Alg H (λ x → List String → Hefty H x)
-- alg (uniquify_Alg ⦃ w₁ ⦄ ⦃ w₂ ⦄) op ψ k = case▹≡ ⦃ w₁ ⦄ op
--   (λ { (letvar v) pf env → impure {!inj▹ₗ ⦃ w₁ ⦄ (letvar "test")!} (λ x → ψ x (v ∷ env)) (λ x → k x env) } )
--   (λ _ _ → case▹≡ ⦃ w₂ ⦄ op
--     (λ { (var v) pf env → {!!} })
--     λ _ _ env → impure op (λ x → ψ x env) (λ x → k x env))

handle▹ : {H H′ H″ H₀ : Effectᴴ} ⦃ w₁ : H ∼ H₀ ▹ H′ ⦄ → Alg H₀ (Hefty H″) → Alg H′ (Hefty H″) → Alg H (Hefty H″)
alg (handle▹ {H} {H′} {H″} {H₀} ⦃ w ⦄ α β) op ψ k = case▹≡ ⦃ w ⦄ op
  (λ op′ pf →
    let
      ψ′ = subst (λ x → (s : Op x) → Hefty H″ (Ret x s))
        (begin
          Fork H op
        ≡⟨ cong (Fork H) pf ⟩
          Fork H (inj▹ₗ op′)
        ≡⟨ inj▹ₗ-fork≡ ⦃ w ⦄ op′ ⟩
          Fork H₀ op′
        ∎) ψ
      k′ = subst (λ x → x → Hefty H″ _)
        (begin
          Ret H op
        ≡⟨ cong (Ret H) pf ⟩
          Ret H (inj▹ₗ op′)
        ≡⟨ inj▹ₗ-ret≡ ⦃ w ⦄ op′ ⟩
          Ret H₀ op′
        ∎) k
    in alg α op′ ψ′ k′)
  (λ op′ pf →
    let
      ψ′ = subst (λ x → (s : Op x) → Hefty H″ (Ret x s))
        (begin
          Fork H op
        ≡⟨ cong (Fork H) pf ⟩
          Fork H (inj▹ᵣ op′)
        ≡⟨ inj▹ᵣ-fork≡ ⦃ w ⦄ op′ ⟩
          Fork H′ op′
        ∎) ψ
      k′ = subst (λ x → x → Hefty H″ _)
        (begin
          Ret H op
        ≡⟨ cong (Ret H) pf ⟩
          Ret H (inj▹ᵣ op′)
        ≡⟨ inj▹ᵣ-ret≡ ⦃ w ⦄ op′ ⟩
          Ret H′ op′
        ∎) k
    in alg β op′ ψ′ k′)

-- Note: this has strict semantics
-- assumes unique variables
let2set_Alg : ⦃ w₁ : H ∼ (Let ℤ) ▹ H′ ⦄ ⦃ w₂ : H″ ∼ (Lift (SetVar ℤ)) ▹ H′ ⦄ → Alg H (Hefty H″)
let2set_Alg { H } { H′ } { H″ } ⦃ w₁ ⦄ ⦃ w₂ ⦄ = handle▹ ⦃ w₁ ⦄
  (record { alg = λ { (letvar v) ψ k → ψ false >>= λ x → (↑ (setvar v x)) >>= λ _ → ψ true >>= λ y → k y } })
  (record { alg = λ op ψ k → impure (inj▹ᵣ op)
    (subst (λ x → (s : Op x) → Hefty H″ (Ret x s)) (sym $ inj▹ᵣ-fork≡ ⦃ w₂ ⦄ op) ψ)
    (subst (λ x → x → Hefty H″ _) (sym $ inj▹ᵣ-ret≡ ⦃ w₂ ⦄ op) k) })

--   (λ{ (letvar v) pf →
--     let
--       ψ′ = subst (λ x → (s : Op x) → Hefty H″ (Ret x s))
--         (begin
--           Fork H op
--         ≡⟨ cong (Fork H) pf ⟩
--           Fork H (inj▹ₗ (letvar v))
--         ≡⟨ inj▹ₗ-fork≡ ⦃ w₁ ⦄ (letvar v) ⟩
--           Fork (Let ℤ) (letvar v)
--         ∎) ψ
--       k′ = subst (λ x → x → Hefty H″ _)
--         (begin
--           Ret H op
--         ≡⟨ cong (Ret H) pf ⟩
--           Ret H (inj▹ₗ (letvar v))
--         ≡⟨ inj▹ₗ-ret≡ ⦃ w₁ ⦄ (letvar v) ⟩
--           Ret (Let ℤ) (letvar v)
--         ∎) k
--     in ψ′ false >>= λ x → (↑ (setvar v x)) >>= λ _ → ψ′ true >>= λ y → k′ y
--     })
--   (λ op′ pf →
--     let
--       ψ′ = subst (λ x → (s : Op x) → Hefty H″ (Ret x s))
--         (begin
--           Fork H op
--         ≡⟨ cong (Fork H) pf ⟩
--           Fork H (inj▹ᵣ op′)
--         ≡⟨ inj▹ᵣ-fork≡ ⦃ w₁ ⦄ op′ ⟩
--           Fork H′ op′
--         ≡⟨ sym $ inj▹ᵣ-fork≡ ⦃ w₂ ⦄ op′ ⟩
--           Fork H″ (inj▹ᵣ op′)
--         ∎) ψ
--       k′ = subst (λ x → x → Hefty H″ _)
--         (begin
--           Ret H op
--         ≡⟨ cong (Ret H) pf ⟩
--           Ret H (inj▹ᵣ op′)
--         ≡⟨ inj▹ᵣ-ret≡ ⦃ w₁ ⦄ op′ ⟩
--           Ret H′ op′
--         ≡⟨ (sym $ inj▹ᵣ-ret≡ ⦃ w₂ ⦄ op′) ⟩
--           Ret H″ (inj▹ᵣ op′)
--         ∎) k
--     in impure (inj▹ᵣ op′) ψ′ k′ )

-- TODO:
--  [x] Weaken let2set_Alg
--  [x] Change let to have two higher-order arguments
--  [ ] Uniquify variables, try de Bruijn + readable names
--  [ ] More types than just ℤ (Intrinsically typed AST?)
--  [ ] Stack allocation → X86
--  [ ] Bigger language (e.g. if statement)
--  [ ] Correctness proofs

data Atom : Set where
  AInt : ℤ → Atom
  AVar : String → Atom

data CExp : Set where
  CAtom : Atom → CExp
  CRead : CExp
  CNeg  : Atom → CExp
  CAdd  : Atom → Atom → CExp
  CSub  : Atom → Atom → CExp

data Stmt : Set where
  Assign : String → CExp → Stmt

data CVar : Set where
  Seq : Stmt → CVar → CVar
  Return : CExp → CVar


