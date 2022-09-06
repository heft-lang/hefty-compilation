{-# OPTIONS --overlapping-instances --instance-search-depth=10 #-}

module Hefty where

open import Algebraic

open import Function hiding (_⟨_⟩_)
import Function.Inverse using (_↔_)
open import Level hiding (Lift)
open import Agda.Primitive
open import Data.Empty
open import Data.Unit
open import Data.Bool hiding (T)
open import Data.Sum
open import Data.Maybe hiding (_>>=_)
open import Data.Nat hiding (_⊔_)
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])
open import Data.Product hiding (_,_)

open Abbreviation using (hThrow; ♯_)

module HeftyModule where
  open FreeModule hiding (_>>=_; _>>_) renaming (‵throw to ‵throw₀)

  record Effectᴴ : Set₁ where
    field  Op     : Set
           Fork   : Op → Effect
           Ret    : Op → Set

  open Effectᴴ
  open Effect

  variable H H′ H″ H‴ H₀ H₁ H₂ H₃ H₄ : Effectᴴ

  private
    variable
      m n : Level
      A B C D X Y Z : Set n
      F F₀ F₁ F₂ F₃ G : Set n → Set (n ⊔ m)

  data Hefty (H : Effectᴴ) (A : Set) : Set where
    pure    :  A → Hefty H A
    impure  :  (op  : Op H)
               (ψ   : (s : Op (Fork H op)) → Hefty H (Ret (Fork H op) s))
               (k   : Ret H op → Hefty H A)
            →  Hefty H A

  Lift : Effect → Effectᴴ
  Op     (Lift ε)    = Op ε
  Fork   (Lift ε) _  = Nil
  Ret    (Lift ε)    = Ret ε

  infixr 12 _∔_

  _∔_ : Effectᴴ → Effectᴴ → Effectᴴ
  Op     (H₁ ∔ H₂)                = Op H₁ ⊎ Op H₂
  Fork   (H₁ ∔ H₂)                = [ Fork H₁  , Fork H₂  ]
  Ret    (H₁ ∔ H₂)                = [ Ret H₁   , Ret H₂   ]

  data _∼_▹_ : Effectᴴ → Effectᴴ → Effectᴴ → Set₁ where
    insert  :                 (H₀ ∔ H′)  ∼ H₀ ▹ H′
    sift    : H ∼ H₀ ▹ H′  →  (H₁ ∔ H)   ∼ H₀ ▹ (H₁ ∔ H′)

  instance  insert▹ : (H₀ ∔ H′) ∼ H₀ ▹ H′
            insert▹ = insert

            sift▹ : ⦃ H ∼ H₀ ▹ H′ ⦄  →  (H₁ ∔ H)   ∼ H₀ ▹ (H₁ ∔ H′)
            sift▹ ⦃ w ⦄ = sift w

  inj▹ₗ  :  ⦃ H ∼ H₀ ▹ H′ ⦄ → Op H₀  → Op H
  inj▹ᵣ  :  ⦃ H ∼ H₀ ▹ H′ ⦄ → Op H′  → Op H

  inj▹ₗ ⦃ insert ⦄  = inj₁
  inj▹ₗ ⦃ sift p ⦄  = inj₂ ∘ inj▹ₗ ⦃ p ⦄

  inj▹ᵣ ⦃ insert ⦄  = inj₂
  inj▹ᵣ ⦃ sift p ⦄  = [ inj₁ , inj₂ ∘ inj▹ᵣ ⦃ p ⦄ ]

  case▹  :  ⦃ H ∼ H₀ ▹ H′ ⦄
         →  Op H
         →  (Op H₀ → B)
         →  (Op H′ → B)
         →  B
  case▹ ⦃ insert ⦄ x f g = [ f , g ] x
  case▹ ⦃ sift p ⦄ x f g = [ g ∘ inj₁ , (λ y → case▹ ⦃ p ⦄ y f (g ∘ inj₂ )) ] x

  case▹≡  :  ⦃ w : H ∼ H₀ ▹ H′ ⦄
         →  (op : Op H)
         →  ((op′ : Op H₀) → op ≡ inj▹ₗ op′ → B)
         →  ((op′ : Op H′) → op ≡ inj▹ᵣ op′ → B)
         →  B
  case▹≡ ⦃ w = insert ⦄ (inj₁ x) f g = f x refl
  case▹≡ ⦃ w = insert ⦄ (inj₂ y) f g = g y refl
  case▹≡ ⦃ w = sift p ⦄ (inj₁ x) f g = g (inj₁ x) refl
  case▹≡ ⦃ w = sift p ⦄ (inj₂ y) f g = case▹≡ ⦃ p ⦄ y (λ op′ → f op′ ∘ cong inj₂) (λ op′ → g (inj₂ op′) ∘ cong inj₂)

  inj▹ₗ-ret≡ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ (op : Op H₀)
             → Ret H (inj▹ₗ op) ≡ Ret H₀ op
  inj▹ₗ-ret≡ ⦃ insert ⦄ _  = refl
  inj▹ₗ-ret≡ ⦃ sift p ⦄    = inj▹ₗ-ret≡ ⦃ p ⦄

  inj▹ᵣ-ret≡ : ⦃ p : H ∼ H₀ ▹ H′ ⦄ (op : Op H′)
            → Ret H (inj▹ᵣ op) ≡ Ret H′ op
  inj▹ᵣ-ret≡ ⦃ insert ⦄ op  = refl
  inj▹ᵣ-ret≡ ⦃ sift p ⦄     = [ (λ _ → refl) , inj▹ᵣ-ret≡ ⦃ p ⦄ ]

  inj▹ₗ-fork≡ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ (op : Op H₀)
                → Fork H (inj▹ₗ op) ≡ Fork H₀ op
  inj▹ₗ-fork≡ ⦃ insert ⦄ _  = refl
  inj▹ₗ-fork≡ ⦃ sift p ⦄    = inj▹ₗ-fork≡ ⦃ p ⦄

  inj▹ᵣ-fork≡ : ⦃ p : H ∼ H₀ ▹ H′ ⦄ (op : Op H′)
                → Fork H (inj▹ᵣ op) ≡ Fork H′ op
  inj▹ᵣ-fork≡ ⦃ insert ⦄ op  = refl
  inj▹ᵣ-fork≡ ⦃ sift p ⦄     = [ (λ _ → refl) , inj▹ᵣ-fork≡ ⦃ p ⦄ ]

  inj▹ₗ-prong≡ : ⦃ p : H ∼ H₀ ▹ H′ ⦄ {op : Op H₀} (b : Op (Fork H (inj▹ₗ op)))
                → Ret (Fork H (inj▹ₗ op)) b ≡ Ret (Fork H₀ op) (subst Op (inj▹ₗ-fork≡ ⦃ p ⦄ op) b)
  inj▹ₗ-prong≡ ⦃ insert ⦄ op  = refl
  inj▹ₗ-prong≡ ⦃ p = sift p ⦄ {op} b = inj▹ₗ-prong≡ ⦃ p ⦄ b

  inj▹ₗ-prong2≡ : ⦃ p : H ∼ H₀ ▹ H′ ⦄ {op : Op H₀} (b : Op (Fork H₀ op))
                → Ret (Fork H₀ op) b ≡ Ret (Fork H (inj▹ₗ op)) (subst Op (sym $ inj▹ₗ-fork≡ ⦃ p ⦄ op) b)
  inj▹ₗ-prong2≡ ⦃ insert ⦄ op  = refl
  inj▹ₗ-prong2≡ ⦃ p = sift p ⦄ {op} b = inj▹ₗ-prong2≡ ⦃ p ⦄ b

  inj▹ᵣ-prong2≡ : ⦃ p : H ∼ H₀ ▹ H′ ⦄ {op : Op H′} (b : Op (Fork H′ op))
                → Ret (Fork H′ op) b ≡ Ret (Fork H (inj▹ᵣ op)) (subst Op (sym $ inj▹ᵣ-fork≡ ⦃ p ⦄ op) b)
  inj▹ᵣ-prong2≡ ⦃ insert ⦄ op  = refl
  inj▹ᵣ-prong2≡ ⦃ p = sift p ⦄ {inj₁ x} b = refl
  inj▹ᵣ-prong2≡ ⦃ p = sift p ⦄ {inj₂ x} b = inj▹ᵣ-prong2≡ ⦃ p ⦄ b

  inj▹ᵣ-prong≡ : ⦃ p : H ∼ H₀ ▹ H′ ⦄ {op : Op H′} (b : Op (Fork H (inj▹ᵣ op)))
               → Ret (Fork H (inj▹ᵣ op)) b ≡ Ret (Fork H′ op) (subst Op (inj▹ᵣ-fork≡ ⦃ p ⦄ op) b)
  inj▹ᵣ-prong≡ ⦃ insert ⦄ op  = refl
  inj▹ᵣ-prong≡ ⦃ p = sift p ⦄ {inj₁ x} b = refl
  inj▹ᵣ-prong≡ ⦃ p = sift p ⦄ {inj₂ y} b = inj▹ᵣ-prong≡ ⦃ p ⦄ b

  proj-ret▹ₗ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ {op : Op H₀} → Ret H (inj▹ₗ op) → Ret H₀ op
  proj-ret▹ₗ ⦃ w = insert ⦄ = id
  proj-ret▹ₗ ⦃ w = sift w ⦄ = proj-ret▹ₗ ⦃ w ⦄

  proj-ret2▹ₗ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ {op : Op H₀} → Ret H₀ op → Ret H (inj▹ₗ op)
  proj-ret2▹ₗ ⦃ w = insert ⦄ = id
  proj-ret2▹ₗ ⦃ w = sift w ⦄ = proj-ret2▹ₗ ⦃ w ⦄

  proj-ret▹ᵣ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ {op : Op H′} → Ret H (inj▹ᵣ op) → Ret H′ op
  proj-ret▹ᵣ ⦃ w = insert ⦄ = id
  proj-ret▹ᵣ ⦃ w = sift w ⦄ {op = inj₁ x} = id
  proj-ret▹ᵣ ⦃ w = sift w ⦄ {op = inj₂ y} = proj-ret▹ᵣ ⦃ w ⦄

  proj-ret2▹ᵣ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ {op : Op H′} → Ret H′ op → Ret H (inj▹ᵣ op)
  proj-ret2▹ᵣ ⦃ w = insert ⦄ = id
  proj-ret2▹ᵣ ⦃ w = sift w ⦄ {op = inj₁ x} = id
  proj-ret2▹ᵣ ⦃ w = sift w ⦄ {op = inj₂ y} = proj-ret2▹ᵣ ⦃ w ⦄

  proj-fork▹ₗ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ {op : Op H₀}
                → ((b : Op (Fork H₀ op)) → Hefty H (Ret (Fork H₀ op) b))
                → ((b : Op (Fork H (inj▹ₗ op))) → Hefty H (Ret (Fork H (inj▹ₗ op)) b))
  proj-fork▹ₗ ⦃ w ⦄ {op} f b  =
    let x = f (subst Op (inj▹ₗ-fork≡ ⦃ w ⦄ op) b) in
    subst (Hefty _) (sym $ inj▹ₗ-prong≡ ⦃ w ⦄ b) x

  proj-fork2▹ₗ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ {op : Op H₀}
                → ((b : Op (Fork H (inj▹ₗ op))) → Hefty H″ (Ret (Fork H (inj▹ₗ op)) b))
                → ((b : Op (Fork H₀ op)) → Hefty H″ (Ret (Fork H₀ op) b))
  proj-fork2▹ₗ ⦃ w ⦄ {op} f b  =
    let x = f (subst Op (sym $ inj▹ₗ-fork≡ ⦃ w ⦄ op) b) in
    subst (Hefty _) (sym $ inj▹ₗ-prong2≡ ⦃ w ⦄ b) x

  proj-fork▹ᵣ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ {op : Op H′}
                → ((b : Op (Fork H′ op)) → Hefty H″ (Ret (Fork H′ op) b))
                → ((b : Op (Fork H (inj▹ᵣ op))) → Hefty H″ (Ret (Fork H (inj▹ᵣ op)) b))
  proj-fork▹ᵣ ⦃ w ⦄ {op} f b  =
    let x = f (subst Op (inj▹ᵣ-fork≡ ⦃ w ⦄ op) b) in
    subst (Hefty _) (sym $ inj▹ᵣ-prong≡ ⦃ w ⦄ b) x

  proj-fork2▹ᵣ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ {op : Op H′}
                → ((b : Op (Fork H (inj▹ᵣ op))) → Hefty H″ (Ret (Fork H (inj▹ᵣ op)) b))
                → ((b : Op (Fork H′ op)) → Hefty H″ (Ret (Fork H′ op) b))
  proj-fork2▹ᵣ ⦃ w ⦄ {op} f b  =
    let x = f (subst Op (sym $ inj▹ᵣ-fork≡ ⦃ w ⦄ op) b) in
    subst (Hefty _) (sym $ inj▹ᵣ-prong2≡ ⦃ w ⦄ b) x

  ↑_ : ⦃ w : H ∼ Lift ε ▹ H′ ⦄ → (op : Op ε) → Hefty H (Ret ε op)
  ↑_ ⦃ w ⦄ op =
    impure (inj▹ₗ ⦃ w ⦄ op) (proj-fork▹ₗ ⦃ w ⦄ (λ b → ⊥-elim b)) (pure ∘ proj-ret▹ₗ ⦃ w ⦄)

  -- data CatchOp̅ : Set₁ where
  --   catch̅ : Set → CatchOp̅

  -- record Effectᴴ⅋ : Set₂ where
  --   field  Op     : Set₁
  --          Fork   : Op → Effect
  --          Ret    : Op → Set
  -- open Effectᴴ⅋

  -- Catch̅ : Effectᴴ⅋
  -- Op     Catch̅ = CatchOp̅
  -- Fork   Catch̅ (catch̅ A)  = record
  --   { Op = Bool; Ret = λ _ → A }
  -- Ret    Catch̅ (catch̅ A)  = A

  record Universe : Set₁ where
    field  T    : Set
           ⟦_⟧  : T → Set

  open Universe ⦃ ... ⦄

  data CatchOp (T : Set) : Set where
    catch : T → CatchOp T

  Catch : ⦃ u : Universe ⦄ → Effectᴴ
  Op     Catch = CatchOp T
  Fork   Catch (catch t)  = record
    { Op = Bool; Ret = λ _ → ⟦ t ⟧ }
  Ret    Catch (catch t)  = ⟦ t ⟧

  ‵catch   : ⦃ u : Universe ⦄ ⦃ w : H ∼ Catch ▹ H′ ⦄ {t : T} 
           → Hefty H ⟦ t ⟧ → Hefty H ⟦ t ⟧  → Hefty H ⟦ t ⟧
  ‵catch ⦃ w = w ⦄ m₁ m₂  =
    impure
      (inj▹ₗ (catch _))
      (proj-fork▹ₗ ⦃ w ⦄ (λ b → if b then m₁ else m₂))
      (pure ∘ proj-ret▹ₗ ⦃ w ⦄)

  record Alg (H : Effectᴴ) (G : Set → Set) : Set₁ where
    constructor mkAlg
    field alg  :  (op  : Op H)
                  (ψ   : (s : Op (Fork H op)) → G (Ret (Fork H op) s))
                  (k   : Ret H op → G A)
               →  G A
  open Alg

  cataᴴ : (∀ {A} → A → F A) → Alg H F → Hefty H A → F A
  cataᴴ g a (pure x)         = g x
  cataᴴ g a (impure op ψ k)  = alg a op (cataᴴ g a ∘ ψ) (cataᴴ g a ∘ k)

  _>>=_ : Hefty H A → (A → Hefty H B) → Hefty H B
  pure x         >>= g = g x
  impure op ψ k  >>= g = impure op ψ (λ x → k x >>= g)

  _>>_ : Hefty H A → Hefty H B → Hefty H B
  m₁ >> m₂ = m₁ >>= λ _ → m₂

  hmap : (A → B) → Hefty H A → Hefty H B
  hmap f (pure x) = pure (f x)
  hmap f (impure op ψ k) = impure op ψ (hmap f ∘ k)

  -- catch⅋ : ⦃ w : ε ∼ Throw ▸ ε′ ⦄ → Free ε A → Free ε A → Free ε A
  -- catch⅋ m₁ m₂ = (♯ (handle₀ hThrow m₁)) >>=⅋ (maybe pure m₂)
  --   where open FreeModule using () renaming (_>>=_ to _>>=⅋_)

  Elaboration : Effectᴴ → Effect → Set₁
  Elaboration H ε = Alg H (Free ε)

  infixr 12 _⋎_
  _⋎_ : Alg H₁ F → Alg H₂ F → Alg (H₁ ∔ H₂) F
  alg (A₁ ⋎ A₂) (inj₁ op) = alg A₁ op
  alg (A₁ ⋎ A₂) (inj₂ op) = alg A₂ op

module ElabModule where
  open FreeModule hiding (_>>=_; _>>_)
  open HeftyModule hiding (_>>=_; _>>_)
  open Alg
  open Inverse ⦃ ... ⦄
  open Universe ⦃ ... ⦄

  variable A : Set

  elaborate : Elaboration H ε → Hefty H A → Free ε A
  elaborate = cataᴴ pure

  module _ where
    open FreeModule using (_>>=_)

    eNil : Elaboration (Lift Nil) ε
    alg eNil ()

    eCatch : ⦃ u : Universe ⦄ ⦃ w : ε ∼ Throw ▸ ε′ ⦄ →  Elaboration Catch ε
    alg eCatch (catch t) ψ k = let m₁ = ψ true; m₂ = ψ false in
      (♯ (handle₀ hThrow m₁)) >>= maybe k (m₂ >>= k)

  module _ where
    open HeftyModule using (_>>=_; _>>_)
    open import Data.Product using (∃; _,_)
    open import Data.Sum renaming ([_,_] to ⊎[_,_])
    open Universe ⦃ ... ⦄
    open Effectᴴ

    private
      data Type : Set where
        unit  : Type
        num   : Type

    private instance
      TypeUniverse : Universe
      Universe.T TypeUniverse = Type
      Universe.⟦ TypeUniverse ⟧ unit  = ⊤
      Universe.⟦ TypeUniverse ⟧ num   = ℕ

    ‵throwᴴ : ⦃ w : H  ∼  Lift Throw  ▹ H″ ⦄
             → Hefty H A
    ‵throwᴴ ⦃ w ⦄ = (↑ throw) >>= ⊥-elim

    private
      transact  :  ⦃ wₛ  : H  ∼  Lift State  ▹ H′ ⦄ ⦃ wₜ  : H  ∼  Lift Throw  ▹ H″ ⦄ ⦃ w   : H  ∼  Catch       ▹ H‴ ⦄
                →  Hefty H ℕ
      transact = do
        ↑ (put 1)
        ‵catch (do ↑ (put 2); (↑ throw) >>= ⊥-elim) (pure tt)
        ↑ get

    data Type⅋ : Set where
      unit⅋  : Type⅋
      num⅋   : Type⅋

    TypeUniverse⅋ : Universe
    T    ⦃ TypeUniverse⅋ ⦄ = Type
    ⟦_⟧  ⦃ TypeUniverse⅋ ⦄  unit  = ⊤
    ⟦_⟧  ⦃ TypeUniverse⅋ ⦄  num   = ℕ

    eLift : ⦃ ε ∼ ε₀ ▸ ε′ ⦄ → Elaboration (Lift ε₀) ε
    alg (eLift ⦃ w ⦄) op ψ k = impure (inj▸ₗ op) (k ∘ proj-ret▸ₗ ⦃ w ⦄)

    transact-elab : Elaboration (Lift State ∔ Lift Throw ∔ Catch ∔ Lift Nil) (State ⊕ Throw ⊕ Nil)
    transact-elab = eLift ⋎ eLift ⋎ eCatch ⋎ eNil

    test-transact : end (handle₀ hThrow (handle hSt (elaborate transact-elab transact) 0))
                    ≡ just 2
    test-transact = refl

    Catch⅋ = Catch ⦃ TypeUniverse ⦄

    eCatch₁ : ⦃ u : Universe ⦄ ⦃ w : ε ∼ Throw ▸ ε′ ⦄ →  Elaboration Catch⅋ ε
    alg eCatch₁ (catch t) ψ k = (ψ true) >>=⅋ k
      where open FreeModule using () renaming (_>>=_ to _>>=⅋_)

    transact-elab₁ : Elaboration (Lift State ∔ Lift Throw ∔ Catch ∔ Lift Nil) (State ⊕ Throw ⊕ Nil)
    transact-elab₁ = eLift ⋎ eLift ⋎ eCatch₁ ⋎ eNil

    test-transact₁ : end (handle₀ hThrow (handle hSt (elaborate transact-elab₁ transact) 0))
                     ≡ nothing
    test-transact₁ = refl

  module _ where
    auto-elab₀ : ⦃ E₁ : Elaboration H₁ ε ⦄ ⦃ E₂ : Elaboration H₂ ε ⦄ → Elaboration (H₁ ∔ H₂) ε
    auto-elab₀ ⦃ E₁ ⦄ ⦃ E₂ ⦄ = E₁ ⋎ E₂

    record Elab (H : Effectᴴ) (ε : Effect) : Set₁ where
      field orate : Alg H (Free ε)
    open Elab

    elab  : Elab H ε → Hefty H A → Free ε A
    elab = elaborate ∘ orate

    instance
      eLift′ : ⦃ ε ∼ ε₀ ▸ ε′ ⦄ → Elab (Lift ε₀) ε
      orate eLift′ = eLift

      eNil′ : Elab (Lift Nil) ε
      orate eNil′ = eNil

    private instance
      eCatch′ : ⦃ u : Universe ⦄ → ⦃ w : ε ∼ Throw ▸ ε′ ⦄ →  Elab (Catch ⦃ u ⦄) ε
      orate eCatch′ = eCatch

    instance
      auto-elab : ⦃ E₁ : Elab H₁ ε ⦄ ⦃ E₂ : Elab H₂ ε ⦄ → Elab (H₁ ∔ H₂) ε
      orate (auto-elab ⦃ E₁ ⦄ ⦃ E₂ ⦄) = (orate E₁) ⋎ (orate E₂)

    module _ ⦃ u : Universe ⦄ where private
      transact-elab′ : Elaboration (Lift State ∔ Lift Throw ∔ Catch ∔ Lift Nil) (State ⊕ Throw ⊕ Nil)
      transact-elab′ = orate auto-elab
