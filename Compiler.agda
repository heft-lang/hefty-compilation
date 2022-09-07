module Compiler where

open import Data.Integer using ( ℤ ; _-_ ; -_ ; _+_ )
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

module Effects where
  open Universe ⦃ ... ⦄

  variable
    A : Set

  -- Arith

  data ArithOp : Set where
    int : ℤ → ArithOp
    neg : ℤ → ArithOp
    add : ℤ → ℤ → ArithOp
    sub : ℤ → ℤ → ArithOp

  Arith : Effect
  Op  Arith           = ArithOp
  Ret Arith (int n)   = ℤ
  Ret Arith (neg x)   = ℤ
  Ret Arith (add x y) = ℤ
  Ret Arith (sub x y) = ℤ

  -- Read

  data ReadOp : Set where
    read : ReadOp

  Read : Effect
  Op   Read       = ReadOp
  Ret  Read read  = ℤ

  ‵read : ⦃ ε ∼ Read ▸ ε′ ⦄ → Free ε ℤ
  ‵read ⦃ w ⦄ = impure (inj▸ₗ read) (pure ∘ proj-ret▸ₗ ⦃ w ⦄)

  -- Var

  data VarOp : Set where
    var : String → VarOp

  Var : Set → Effect
  Op (Var T) = VarOp
  Ret (Var T) (var _) = T

  ‵var : ⦃ w : ε ∼ Var A ▸ ε′ ⦄ → String → Free ε A
  ‵var ⦃ w ⦄ v = impure (inj▸ₗ (var v)) (pure ∘ proj-ret▸ₗ ⦃ w ⦄)

  -- Let

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

  -- Assign

  data AssignOp (A : Set) : Set where
    assign : String → A → AssignOp A

  Assign : Set → Effect
  Op (Assign A) = AssignOp A
  Ret (Assign A) (assign _ _) = ⊤

  ‵assign : ⦃ ε ∼ Assign A ▸ ε′ ⦄ → String → A → Free ε ⊤
  ‵assign ⦃ w ⦄ v x = impure (inj▸ₗ (assign v x)) (pure ∘ proj-ret▸ₗ ⦃ w ⦄)

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

⟦_⟧ :
  ⦃ w₁ : H ∼ Lift Arith ▹ H₁ ⦄
  ⦃ w₂ : H ∼ Lift Read ▹ H₂ ⦄
  ⦃ w₃ : H ∼ (Let ℤ) ▹ H₃ ⦄
  ⦃ w₄ : H ∼ Lift (Var ℤ) ▹ H₄ ⦄ →
  LExp → Hefty H ℤ
⟦ LInt n ⟧ = ↑ (int n)
⟦ LRead ⟧ = ↑ read
⟦ LNeg x ⟧ = ⟦ x ⟧ >>= λ x → ↑ (neg x)
⟦ LAdd x y ⟧ = ⟦ x ⟧ >>= λ x → ⟦ y ⟧ >>= λ y → ↑ (add x y)
⟦ LSub x y ⟧ = ⟦ x ⟧ >>= λ x → ⟦ y ⟧ >>= λ y → ↑ (sub x y)
⟦ LVar v ⟧ =  ↑ (var v)
⟦ LLet v x y ⟧ =  ‵letvar v ⟦ x ⟧ ⟦ y ⟧

open Alg

weakenᵣ : { F : Set → Set } ⦃ w : H ∼ H₀ ▹ H′ ⦄ → Alg H F → Alg H′ F
alg (weakenᵣ {_} {_} {_} {F} α) op ψ k = alg α
  (inj▹ᵣ op)
  (subst (λ x → (s : Op x) → F (Ret x s)) (sym $ inj▹ᵣ-fork≡ op) ψ)
  (subst (λ x → x → F _) (sym $ inj▹ᵣ-ret≡ op) k)

gensym : List String → String → String
gensym xs x with length (filterᵇ (x ==_) xs)
... | 0 = x
... | n = x ++ show n

-- Only uniquifies variables that occur in the same scope (i.e. those that would be shadowed)
uniquify_Alg :
  ⦃ w₁ : H ∼ (Let A) ▹ H′ ⦄ ⦃ w₂ : H′ ∼ Lift (Var A) ▹ H″ ⦄ ⦃ w₃ : H ∼ Lift (Var A) ▹ H‴ ⦄ →
  Alg H (λ x → List String → Hefty H x)
uniquify_Alg ⦃ w₁ ⦄ ⦃ w₂ ⦄ ⦃ w₃ ⦄ =
  handle▹ ⦃ w₁ ⦄
    (mkAlg λ { (letvar v) ψ k env → ‵letvar (gensym env v) (ψ false env) (ψ true (v ∷ env)) >>= λ x → k x env })
    (handle▹ ⦃ w₂ ⦄
      (mkAlg λ { (var v) _ k env → (↑_ ⦃ w₃ ⦄ (var (gensym env v))) >>= λ x → k x env })
      (weakenᵣ ⦃ w₂ ⦄ (weakenᵣ ⦃ w₁ ⦄ (mkAlg λ op ψ k env → impure op (λ x → ψ x env) (λ x → k x env)))))

-- Note: this has strict semantics
-- assumes unique variable names
let2set_Alg : ⦃ w₁ : H ∼ (Let ℤ) ▹ H′ ⦄ ⦃ w₂ : H″ ∼ (Lift (Assign ℤ)) ▹ H′ ⦄ → Alg H (Hefty H″)
let2set_Alg { H } { H′ } { H″ } ⦃ w₁ ⦄ ⦃ w₂ ⦄ = handle▹ ⦃ w₁ ⦄
  (mkAlg (λ { (letvar v) ψ k → ψ false >>= λ x → (↑ (assign v x)) >>= λ _ → ψ true >>= λ y → k y } ))
  (mkAlg (λ op ψ k → impure (inj▹ᵣ op)
    (subst (λ x → (s : Op x) → Hefty H″ (Ret x s)) (sym $ inj▹ᵣ-fork≡ ⦃ w₂ ⦄ op) ψ)
    (subst (λ x → x → Hefty H″ _) (sym $ inj▹ᵣ-ret≡ ⦃ w₂ ⦄ op) k) ))

-- TODO:
--  [x] Weaken let2set_Alg
--  [x] Change let to have two higher-order arguments
--  [x] Split out common structure of let2set_Alg
--  [x] Uniquify variables
--  [ ] Stack allocation → X86
--  [ ] More types than just ℤ (Intrinsically typed AST?)
--  [ ] Bigger language (e.g. if statement)
--  [ ] Correctness proofs


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
