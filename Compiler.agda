module Compiler where

open import Data.Integer using ( ℤ ; _-_ ; -_ ; _+_ )
open import Data.String using ( String )
open import Data.Unit
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

  data LetOp : Set where
    letvar : String → LetOp

  Let : Set → Effectᴴ
  Op     (Let _) = LetOp
  Fork   (Let A) (letvar _)  = record
    { Op = ⊤; Ret = λ _ → A }
  Ret    (Let _) (letvar _)  = ⊤

  ‵letvar   : ⦃ w : H ∼ (Let A) ▹ H′ ⦄
           → String → Hefty H A  → Hefty H ⊤
  ‵letvar ⦃ w = w ⦄ v m  =
    impure
      (inj▹ₗ (letvar v))
      (proj-fork▹ₗ ⦃ w ⦄ (λ _ → m))
      (pure ∘ proj-ret▹ₗ ⦃ w ⦄)

  data SetVarOp (A : Set) : Set where
    -- getvar : String → SetVarOp A
    setvar : String → A → SetVarOp A

  SetVar : Set → Effect
  Op (SetVar A) = SetVarOp A
  -- Ret (SetVar A) (getvar _) = A
  Ret (SetVar A) (setvar _ _) = ⊤

  -- ‵getvar : ⦃ ε ∼ SetVar A ▸ ε′ ⦄ → String → Free ε A
  -- ‵getvar ⦃ w ⦄ v = impure (inj▸ₗ (getvar v)) (pure ∘ proj-ret▸ₗ ⦃ w ⦄)

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
⟦ LLet v x y ⟧ =  ‵letvar v ⟦ x ⟧ >>= λ _ → ⟦ y ⟧

open Alg

id_Alg : Alg H (Hefty H)
alg id_Alg op ψ k = impure op ψ k

coerce : { B : Set } → A → A ≡ B → B
coerce x refl = x

-- let2set_Alg : ⦃ w₁ : H ∼ H₀ ▹ H′ ⦄ → Alg H (Hefty (H′ ∔ H″)

-- Note: this has strict semantics
let2set_Alg : ⦃ w₁ : H ∼ (Let ℤ) ▹ H′ ⦄ ⦃ w₂ : H″ ∼ (Lift (SetVar ℤ)) ▹ H′ ⦄ → Alg H (Hefty H″)
alg (let2set_Alg { H } { H′ } { H″ } ⦃ w₁ ⦄ ⦃ w₂ ⦄) op ψ k = case▹≡ ⦃ w₁ ⦄ op
  (λ{ (letvar v) pf →
    let
      ψ′ = subst (λ x → (s : Op x) → Hefty H″ (Ret x s))
        (begin
          Fork H op
        ≡⟨ cong _ pf ⟩
          Fork H (inj▹ₗ (letvar v))
        ≡⟨ inj▹ₗ-fork≡ ⦃ w₁ ⦄ (letvar v) ⟩
          Fork (Let ℤ) (letvar v)
        ∎) ψ
      k′ = subst (λ x → x → Hefty H″ _)
        (begin
          Ret H op
        ≡⟨ cong _ pf ⟩
          Ret H (inj▹ₗ (letvar v))
        ≡⟨ inj▹ₗ-ret≡ ⦃ w₁ ⦄ (letvar v) ⟩
          Ret (Let ℤ) (letvar v)
        ∎) k
    in ψ′ tt >>= λ x → (↑ (setvar v x)) >>= λ _ → k′ tt
    })
  (λ op′ pf →
    let
      ψ′ = subst (λ x → (s : Op x) → Hefty H″ (Ret x s))
        (begin
          Fork H op
        ≡⟨ cong _ pf ⟩
          Fork H (inj▹ᵣ op′)
        ≡⟨ inj▹ᵣ-fork≡ ⦃ w₁ ⦄ op′ ⟩
          Fork H′ op′
        ≡⟨ sym $ inj▹ᵣ-fork≡ ⦃ w₂ ⦄ op′ ⟩
          Fork H″ (inj▹ᵣ op′)
        ∎) ψ
      k′ = subst (λ x → x → Hefty H″ _)
        (begin
          Ret H op
        ≡⟨ cong _ pf ⟩
          Ret H (inj▹ᵣ op′)
        ≡⟨ inj▹ᵣ-ret≡ ⦃ w₁ ⦄ op′ ⟩
          Ret H′ op′
        ≡⟨ (sym $ inj▹ᵣ-ret≡ ⦃ w₂ ⦄ op′) ⟩
          Ret H″ (inj▹ᵣ op′)
        ∎) k
    in impure (inj▹ᵣ op′) ψ′ k′ )

-- TODO:
--  * Weaken let2set_Alg
--  * How to do uniquify? Try de Bruijn + readable names
--  * More types than just ℤ (Intrinsically typed AST?)
--  * Stack allocation → X86
--  * Bigger language (e.g. if statement)
--  * Correctness proofs

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


