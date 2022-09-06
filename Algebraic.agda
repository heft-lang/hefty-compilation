module Algebraic where

open import Level
open import Function
open import Data.Empty
open import Data.Unit
open import Data.Bool hiding (_≤_)
open import Data.Maybe using (Maybe; nothing; just; maybe)
open import Data.Sum
open import Data.Nat hiding ( _≤_)
open import Data.Product using (_×_; _,_)
-- open import Data.List
-- open import Data.List.Membership.Propositional
-- open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Effect.Monad
open ≡-Reasoning
open import Postulates.Extensionality

private variable a b c : Level
                 A A′ B B′ C : Set a

module FreeModule where

  -- Effect & Free Monad

  record Effect : Set₁ where
    field  Op   : Set
           Ret  : Op → Set

  open Effect
  variable ε ε′ ε″ ε₀ ε₁ ε₂ ε₃ : Effect

  infixr 12 _⊕_
  _⊕_ : Effect → Effect → Effect
  Op (ε₁ ⊕ ε₂) = Op ε₁ ⊎ Op ε₂
  Ret (ε₁ ⊕ ε₂) = [ Ret ε₁ , Ret ε₂ ]

  data Free (ε : Effect) (A : Set) : Set where
    pure    : A                                      → Free ε A
    impure  : (op : Op ε) (k : Ret ε op → Free ε A)  → Free ε A

  fold  :  (A → B)  →  ((op : Op ε) (k : Ret ε op → B) → B) → Free ε A → B
  fold gen alg (pure x)       = gen x
  fold gen alg (impure op k)  = alg op (fold gen alg ∘ k)

  _>>=_ : Free ε A → (A → Free ε B) → Free ε B
  m >>= g = fold g impure m

  fold≡ : (m : Free ε A) → fold pure impure m ≡ m
  fold≡ (pure x) = refl
  fold≡ (impure op k) = cong (impure op) (extensionality (λ x → fold≡ (k x)))

  fmap : (A → B) → Free ε A → Free ε B
  fmap f = fold (pure ∘ f) impure

  Free-unitₗ-≡ : {x : A} (k : A → Free ε B)
               → pure x >>= k ≡ k x
  Free-unitₗ-≡ _ = refl

  Free-unitᵣ-≡ : (m : Free ε A)
               → m >>= pure ≡ m
  Free-unitᵣ-≡ (pure x) = refl
  Free-unitᵣ-≡ (impure op k) = cong (λ x → impure op x) (extensionality $ λ y → Free-unitᵣ-≡ $ k y) 

  Free-assoc-≡ : (m : Free ε A) (k₁ : A → Free ε B) (k₂ : B → Free ε C)
               → (m >>= k₁) >>= k₂ ≡ m >>= (λ x → (k₁ x) >>= k₂)
  Free-assoc-≡ (pure x) k₁ k₂ = refl
  Free-assoc-≡ (impure op k) k₁ k₂ = cong (λ x → impure op x) (extensionality $ λ x → Free-assoc-≡ (k x) k₁ k₂)

  Free-cong₂ : (m : Free ε A) (k k' : A → Free ε B)
             → (∀ x → k x ≡ k' x)
             → (m >>= k) ≡ (m >>= k')
  Free-cong₂ (pure x) k k' eq = eq _
  Free-cong₂ (impure op k₁) k k' eq = cong (λ x → impure op x) $ extensionality $ λ x →
    cong (λ y → (k₁ x) >>= y) $ extensionality eq

  _>>_ : Free ε A → Free ε B → Free ε B
  m₁ >> m₂ = m₁ >>= λ _ → m₂

  -- Rows

  data _∼_▸_ : Effect → Effect → Effect → Set₁ where
    insert  :                    (ε₀ ⊕ ε′)  ∼ ε₀ ▸ ε′
    sift    :  (ε ∼ ε₀ ▸ ε′)  →  ((ε₁ ⊕ ε)   ∼ ε₀ ▸ (ε₁ ⊕ ε′))

  instance  insert▸ : (ε₀ ⊕ ε′)  ∼ ε₀ ▸ ε′
            insert▸ = insert

            sift▸ : ⦃ ε ∼ ε₀ ▸ ε′ ⦄  →  ((ε₁ ⊕ ε)   ∼ ε₀ ▸ (ε₁ ⊕ ε′))
            sift▸ ⦃ w ⦄ = sift w

  inj▸ₗ  :  ⦃ ε ∼ ε₀ ▸ ε′ ⦄ → Op ε₀  → Op ε
  inj▸ᵣ  :  ⦃ ε ∼ ε₀ ▸ ε′ ⦄ → Op ε′  → Op ε

  inj▸ₗ ⦃ insert ⦄  = inj₁
  inj▸ₗ ⦃ sift p ⦄  = inj₂ ∘ inj▸ₗ ⦃ p ⦄

  inj▸ᵣ ⦃ insert ⦄  = inj₂
  inj▸ᵣ ⦃ sift p ⦄  = [ inj₁ , inj₂ ∘ inj▸ᵣ ⦃ p ⦄ ]

  proj-ret▸ₗ : ⦃ w : ε ∼ ε₀ ▸ ε′ ⦄ {op : Op ε₀} → Ret ε (inj▸ₗ op) → Ret ε₀ op
  proj-ret▸ₗ ⦃ w = insert ⦄ = id
  proj-ret▸ₗ ⦃ w = sift w ⦄ = proj-ret▸ₗ ⦃ w ⦄

  proj-ret▸ᵣ : ⦃ w : ε ∼ ε₀ ▸ ε′ ⦄ {op : Op ε′} → Ret ε (inj▸ᵣ op) → Ret ε′ op
  proj-ret▸ᵣ ⦃ w = insert ⦄ = id
  proj-ret▸ᵣ ⦃ w = sift w ⦄ {op = inj₁ x} = id
  proj-ret▸ᵣ ⦃ w = sift w ⦄ {op = inj₂ y} = proj-ret▸ᵣ ⦃ w ⦄

  -- State
  
  data StateOp : Set where
    put : ℕ →  StateOp
    get :      StateOp
 
  State : Effect
  Op   State          = StateOp
  Ret  State (put n)  = ⊤
  Ret  State get      = ℕ
  
  incr-example : Free State ⊤
  incr-example = impure get (λ n → impure (put (n + 1)) pure)

  ‵put : ⦃ ε ∼ State ▸ ε′ ⦄ → ℕ → Free ε ⊤
  ‵put ⦃ w ⦄ n = impure (inj▸ₗ (put n)) (pure ∘ proj-ret▸ₗ ⦃ w ⦄)

  ‵get : ⦃ ε ∼ State ▸ ε′ ⦄ → Free ε ℕ
  ‵get ⦃ w ⦄ = impure (inj▸ₗ get) (pure ∘ proj-ret▸ₗ ⦃ w ⦄)

  -- Throw
  
  data ThrowOp : Set where
    throw : ThrowOp

  Throw : Effect
  Op   Throw = ThrowOp
  Ret  Throw throw = ⊥

  incr-throw-example₀ : Free (State ⊕ Throw) A
  incr-throw-example₀ =
    impure (inj₁ get) (λ n → impure (inj₁ (put (n + 1))) (λ _ → impure (inj₂ throw) ⊥-elim))
  
  ‵throw : ⦃ ε ∼ Throw ▸ ε′ ⦄ → Free ε A
  ‵throw ⦃ w ⦄ = impure (inj▸ₗ throw) (⊥-elim ∘ proj-ret▸ₗ ⦃ w ⦄)

  incr-throw-example₁ : ⦃ ε ∼ State ▸ ε₁ ⦄ → ⦃ ε ∼ Throw ▸ ε₂ ⦄ → Free ε A
  incr-throw-example₁ = do n ← ‵get; ‵put (n + 1); ‵throw

  -- More helpers

  inj▸ₗ-ret≡ : ⦃ p : ε ∼ ε₀ ▸ ε′ ⦄ (op : Op ε₀)
             → Ret ε (inj▸ₗ op) ≡ Ret ε₀ op
  inj▸ₗ-ret≡ ⦃ insert ⦄ _  = refl
  inj▸ₗ-ret≡ ⦃ sift p ⦄    = inj▸ₗ-ret≡ ⦃ p ⦄

  inj▸ᵣ-ret≡ : ⦃ p : ε ∼ ε₀ ▸ ε′ ⦄ (op : Op ε′)
             → Ret ε (inj▸ᵣ op) ≡ Ret ε′ op
  inj▸ᵣ-ret≡ ⦃ insert ⦄ op  = refl
  inj▸ᵣ-ret≡ ⦃ sift p ⦄     = [ (λ _ → refl) , inj▸ᵣ-ret≡ ⦃ p ⦄ ]


  case▸  :  ⦃ ε ∼ ε₀ ▸ ε′ ⦄
         →  Op ε
         →  (Op ε₀  → B)
         →  (Op ε′  → B)
         →  B
  case▸ ⦃ insert ⦄ x f g = [ f , g ] x
  case▸ ⦃ sift p ⦄ x f g = [ g ∘ inj₁ , (λ y → case▸ ⦃ p ⦄ y f (g ∘ inj₂)) ] x

  case▸≡  :  ⦃ w : ε ∼ ε₀ ▸ ε′ ⦄
         →  (op : Op ε)
         →  ((op′ : Op ε₀) → op ≡ inj▸ₗ op′ → B)
         →  ((op′ : Op ε′) → op ≡ inj▸ᵣ op′ → B)
         →  B
  case▸≡ ⦃ w = insert ⦄ (inj₁ x) f g = f x refl
  case▸≡ ⦃ w = insert ⦄ (inj₂ y) f g = g y refl
  case▸≡ ⦃ w = sift p ⦄ (inj₁ x) f g = g (inj₁ x) refl
  case▸≡ ⦃ w = sift p ⦄ (inj₂ y) f g = case▸≡ ⦃ p ⦄ y (λ op′ → f op′ ∘ cong inj₂) (λ op′ → g (inj₂ op′) ∘ cong inj₂)


  to-front : ⦃ w : ε ∼ ε₀ ▸ ε′ ⦄ → Free ε A → Free (ε₀ ⊕ ε′) A
  to-front {ε₀ = ε₀} ⦃ w ⦄ (pure x) = pure x
  to-front {ε₀ = ε₀} ⦃ insert ⦄ (impure op k) = impure op (to-front ⦃ insert ⦄ ∘ k)
  to-front {ε₀ = ε₀} ⦃ sift w ⦄ (impure (inj₁ op) k) = impure (inj₂ (inj₁ op)) (to-front ⦃ sift w ⦄ ∘ k)
  to-front {ε₀ = ε₀} ⦃ sift {ε = ε} {ε′ = ε′} w ⦄ t@(impure (inj₂ op) k) = case▸≡ ⦃ w ⦄ op
    (λ op′ eq →
      impure
        (inj₁ op′)
        ( to-front ⦃ sift w ⦄
        ∘ k
        ∘ subst id (begin
            Ret ε₀ op′
          ≡⟨ sym (inj▸ₗ-ret≡ ⦃ w ⦄ op′) ⟩
            Ret ε (inj▸ₗ ⦃ w ⦄ op′)
          ≡⟨ sym $ cong (Ret ε) eq ⟩
            Ret ε op
          ∎)))
    (λ op′ eq →
      impure (inj₂ (inj₂ op′))
        ( to-front ⦃ sift w ⦄
        ∘ k
        ∘ subst id (begin
            Ret ε′ op′
          ≡⟨ sym (inj▸ᵣ-ret≡ ⦃ w ⦄ op′) ⟩
            Ret ε (inj▸ᵣ ⦃ w ⦄ op′)
          ≡⟨ (sym $ cong (Ret ε) eq) ⟩
            Ret ε op
          ∎)))

  from-front : ⦃ w : ε ∼ ε₀ ▸ ε′ ⦄ → Free (ε₀ ⊕ ε′) A → Free ε A
  from-front ⦃ w = w ⦄ (pure x) = pure x
  from-front ⦃ w = w ⦄ (impure (inj₁ op) k) = impure (inj▸ₗ op) (from-front ∘ k ∘ proj-ret▸ₗ ⦃ w ⦄)
  from-front ⦃ w = w ⦄ (impure (inj₂ op) k) = impure (inj▸ᵣ op) (from-front ∘ k ∘ proj-ret▸ᵣ ⦃ w ⦄)

  -- Handlers

  record ParameterizedHandler (ε : Effect) (P : Set) (G : Set → Set) : Set₁ where
    field  ret  : {A : Set} → A → P → G A
           hdl  : {A : Set} (op : Op ε) (k : Ret ε op → P → Free ε′ (G A)) → P → Free ε′ (G A)

  open ParameterizedHandler

  private variable P : Set
                   G : Set → Set

  flip⅋ : (B → A → C) → A → B → C
  flip⅋ f x y = f y x

  handle : ⦃ ε ∼ ε₀ ▸ ε′ ⦄ → ParameterizedHandler ε₀ P G → Free ε A → P → Free ε′ (G A)
  handle h  =  fold (λ p → pure ∘ ret h p) [ hdl h , (λ op′ k′ → impure op′ ∘ flip k′) ]
               ∘ to-front

  hSt : ParameterizedHandler State ℕ id
  ret hSt x _ = x
  hdl hSt (put m)  k n = k tt m
  hdl hSt get      k n = k n  n

  record SimpleHandler (ε : Effect) (G : Set → Set) : Set₁ where
    field  ret : ∀ {A} → A → G A
           hdl : ∀ {A} → (op : Op ε) (k : Ret ε op → Free ε′ (G A)) → Free ε′ (G A)
  open SimpleHandler public

  Simple-to-Parameterized :  SimpleHandler ε G → ParameterizedHandler ε ⊤ G
  ret (Simple-to-Parameterized S) x _    = ret S x
  hdl (Simple-to-Parameterized S) op k _ = hdl S op (flip k tt)

  handle₀ : ⦃ ε ∼ ε₀ ▸ ε′ ⦄ → SimpleHandler ε₀ G → Free ε A → Free ε′ (G A)
  handle₀ SH = flip (handle (Simple-to-Parameterized SH)) tt

  -- Nil Effect

  Nil : Effect
  Op   Nil = ⊥
  Ret  Nil = ⊥-elim

  end : Free Nil A → A; end (pure x) = x

  -- More examples

  ‵incr-example : ⦃ ε ∼ State ▸ ε′ ⦄ → Free ε ℕ
  ‵incr-example = do n ← ‵get; ‵put (n + 1); ‵get
  
  incr-test : end (handle hSt ‵incr-example 0) ≡ 1
  incr-test = refl

  hSt₁ : ParameterizedHandler State ℕ (λ X → X × ℕ)
  ret hSt₁ = _,_
  hdl hSt₁ (put m)  k n = k tt  m
  hdl hSt₁ get      k n = k n   n

  incr-test₁ : end (handle hSt₁ ‵incr-example 0) ≡ (1 , 1)
  incr-test₁ = refl

--     data Choice : Effect where
--       choice : Choice Bool

--     ‵choice : ⦃ Choice ▸ R′ ∼ R ⦄ → Free R Bool
--     ‵choice = impure (inj▸ₗ choice) pure

--     example₁ : Free (Choice ∷ State ∷ []) ℕ
--     example₁ = do
--       ‵put 1
--       b ← ‵choice
--       if b then ‵incr else (do ‵incr; ‵incr)
--       ‵get

--     hChoice : ⦃ w : Choice ▸ R′ ∼ R ⦄ → SimpleHandler w List
--     ret hChoice = [_]
--     hdl hChoice choice k = do
--       l₁ ← k true
--       l₂ ← k false
--       pure (l₁ ++ l₂)

--   test₁ : end (handle₀ hChoice (flip (handle hSt) 0 example₁)) ≡ 2 ∷ 3 ∷ []
--   test₁ = refl

--   test₁′ : end (flip (handle hSt) 0 (handle₀ hChoice example₁)) ≡ 2 ∷ 4 ∷ []
--   test₁′ = refl

module AlgebraicityProperty (M : Set → Set) (RM : RawMonad M) where
  open RawMonad RM

  record CatchM (M : Set → Set) : Set₁ where
    field  catch  : M A → M A →  M A
           throw  :              M A

--   module CatchLaw (CO : CatchM M) where
--     open CatchM CO
--     postulate
--
--       Algebraicity-catch  :  (m₁ m₂ : M A) → (k : A → M B)
--                           →  ((catch m₁ m₂) >>= k) ≡ (catch (m₁ >>= k) (m₂ >>= k))

module Abbreviation where
  open FreeModule
  open SimpleHandler

  hThrow : SimpleHandler Throw Maybe
  ret  hThrow          = just
  hdl  hThrow throw k  = pure nothing

  ♯_ : ⦃ ε ∼ ε₀ ▸ ε′ ⦄ → Free ε′ A → Free ε A
  ♯_ ⦃ w ⦄ = fold pure (λ op′ k′ → impure (inj▸ᵣ op′) (k′ ∘ proj-ret▸ᵣ ⦃ w ⦄))

  catch : ⦃ w : ε ∼ Throw ▸ ε′ ⦄ → Free ε A → Free ε A → Free ε A
  catch m₁ m₂ = (♯ (handle₀ hThrow m₁)) >>= (maybe pure m₂)

  record ReaderM (R : Set) (M : Set → Set) : Set₁ where
    field  ask    :                   M R
           local  : (R → R) → M A  →  M A

-- module Scoped where
--   open FreeModule   using (Effect; State; put; get; ε; ε₀; ε′; _∼_▸_; case▸; inj▸ₗ; inj▸ᵣ; throw; Throw; proj-ret▸ₗ; _⊕_; sift; insert;  case▸≡; inj▸ₗ-ret≡; inj▸ᵣ-ret≡)
--   open Effect
-- 
--   private variable γ γ′ γ₀ : Effect
--                    n m : Level
--                    P X Y Z : Set n
--                    F G H : Set n → Set m
-- 
--   data Prog (ε γ : Effect) (A : Set) : Set₁ where
--     return  : A                                                                        → Prog ε γ A
--     call    : (op : Op ε)                                (k : Ret ε op  → Prog ε γ A)  → Prog ε γ A
--     enter   : (op : Op γ)  (sc : Ret γ op → Prog ε γ B)  (k : B         → Prog ε γ A)  → Prog ε γ A
-- 
--   _>>=_ : Prog ε γ A → (A → Prog ε γ B) → Prog ε γ B
--   return x       >>= g = g x
--   call op k      >>= g = call op (λ x → k x >>= g)
--   enter op sc k  >>= g = enter op sc (λ x → k x >>= g)
-- 
--   data CatchOp : Set where
--     catch : CatchOp
-- 
--   Catch : Effect
--   Op   Catch = CatchOp
--   Ret  Catch catch = Bool
-- 
--   ‵catch : ⦃ γ ∼ Catch ▸ γ′ ⦄ → Prog ε γ A → Prog ε γ A → Prog ε γ A
--   ‵catch ⦃ w ⦄ m₁ m₂ = enter (inj▸ₗ catch) (λ b → if (proj-ret▸ₗ ⦃ w ⦄ b) then m₁ else m₂) return
-- 
--   hcata  :  (∀ {X}    → X                                              → F X) 
--          →  (∀ {X}    → (op : Op ε)  (k : Ret ε op → F X)              → F X)
--          →  (∀ {B X}  → (op : Op γ)  (k : Ret γ op → F B) → (B → F X)  → F X)
--          →  Prog ε γ A → F A
--   hcata gen callᴬ enterᴬ (return x)       = gen x
--   hcata gen callᴬ enterᴬ (call op k)      = callᴬ op (hcata gen callᴬ enterᴬ ∘ k)
--   hcata gen callᴬ enterᴬ (enter op sc k)  = enterᴬ  op
--                                                    (hcata gen callᴬ enterᴬ ∘ sc)
--                                                    (hcata gen callᴬ enterᴬ ∘ k )
-- 
--   record SimpleHandlerεγ  (ε γ : Effect) (G : Set → Set) : Set₁ where
--     field
--       ret     :  A → G A
--       hcall   :  (op : Op ε) (k : Ret ε op → Prog ε′ γ′ (G X)) → Prog ε′ γ′ (G X)
--       henter  :  (op : Op γ) (sc : Ret γ op → Prog ε′ γ′ (G B)) (k : B → Prog ε′ γ′ (G X))
--               →  Prog ε′ γ′ (G X)
--       weave   :  (k : C → Prog ε′ γ′ (G X)) (r : G C) → Prog ε′ γ′ (G X)
-- 
--   open SimpleHandlerεγ
-- 
--   to-frontε : ⦃ w : ε ∼ ε₀ ▸ ε′ ⦄ → Prog ε γ A → Prog (ε₀ ⊕ ε′) γ A
--   to-frontε {ε₀ = ε₀} ⦃ w ⦄ (return x) = return x
--   to-frontε {ε₀ = ε₀} ⦃ insert ⦄ (call op k) = call op (to-frontε ⦃ insert ⦄ ∘ k)
--   to-frontε {ε₀ = ε₀} ⦃ sift w ⦄ (call (inj₁ op) k) = call (inj₂ (inj₁ op)) (to-frontε ⦃ sift w ⦄ ∘ k)
--   to-frontε {ε₀ = ε₀} ⦃ sift {ε = ε} {ε′ = ε′} w ⦄ t@(call (inj₂ op) k) = case▸≡ ⦃ w ⦄ op
--     (λ op′ eq →
--       call
--         (inj₁ op′)
--         ( to-frontε ⦃ sift w ⦄
--         ∘ k
--         ∘ subst id (begin
--             Ret ε₀ op′
--           ≡⟨ sym (inj▸ₗ-ret≡ ⦃ w ⦄ op′) ⟩
--             Ret ε (inj▸ₗ ⦃ w ⦄ op′)
--           ≡⟨ sym $ cong (Ret ε) eq ⟩
--             Ret ε op
--           ∎)))
--     (λ op′ eq →
--       call (inj₂ (inj₂ op′))
--         ( to-frontε ⦃ sift w ⦄
--         ∘ k
--         ∘ subst id (begin
--             Ret ε′ op′
--           ≡⟨ sym (inj▸ᵣ-ret≡ ⦃ w ⦄ op′) ⟩
--             Ret ε (inj▸ᵣ ⦃ w ⦄ op′)
--           ≡⟨ (sym $ cong (Ret ε) eq) ⟩
--             Ret ε op
--           ∎)))
--   to-frontε (enter op sc k) = enter op (to-frontε ∘ sc) (to-frontε ∘ k)
-- 
--   to-frontγ : ⦃ w : γ ∼ γ₀ ▸ γ′ ⦄ → Prog ε γ A → Prog ε (γ₀ ⊕ γ′) A
--   to-frontγ {γ₀ = γ₀} ⦃ w ⦄ (return x) = return x
--   to-frontγ (call op k) = call op (to-frontγ ∘ k)
--   to-frontγ {γ₀ = γ₀} ⦃ insert ⦄ (enter op sc k) = enter op (to-frontγ ⦃ insert ⦄ ∘ sc) (to-frontγ ⦃ insert ⦄ ∘ k)
--   to-frontγ {γ₀ = γ₀} ⦃ sift w ⦄ (enter (inj₁ op) sc k) = enter (inj₂ (inj₁ op)) (to-frontγ ⦃ sift w ⦄ ∘ sc) (to-frontγ ⦃ sift w ⦄ ∘ k)
--   to-frontγ {γ₀ = γ₀} ⦃ sift {ε = γ} {ε′ = γ′} w ⦄ t@(enter (inj₂ op) sc k) = case▸≡ ⦃ w ⦄ op
--     (λ op′ eq →
--       enter
--         (inj₁ op′)
--         ( to-frontγ ⦃ sift w ⦄
--         ∘ sc
--         ∘ subst id (begin
--             Ret γ₀ op′
--           ≡⟨ sym (inj▸ₗ-ret≡ ⦃ w ⦄ op′) ⟩
--             Ret γ (inj▸ₗ ⦃ w ⦄ op′)
--           ≡⟨ sym $ cong (Ret γ) eq ⟩
--             Ret γ op
--           ∎))
--         (to-frontγ ⦃ sift w ⦄ ∘ k))
--     (λ op′ eq →
--       enter (inj₂ (inj₂ op′))
--         ( to-frontγ ⦃ sift w ⦄
--         ∘ sc
--         ∘ subst id (begin
--             Ret γ′ op′
--           ≡⟨ sym (inj▸ᵣ-ret≡ ⦃ w ⦄ op′) ⟩
--             Ret γ (inj▸ᵣ ⦃ w ⦄ op′)
--           ≡⟨ (sym $ cong (Ret γ) eq) ⟩
--             Ret γ op
--           ∎))
--         (to-frontγ ⦃ sift w ⦄ ∘ k))
-- 
--   handleεγ₀  :  ⦃ w₁ : ε ∼ ε₀ ▸ ε′ ⦄ → ⦃ w₂ : γ ∼ γ₀ ▸ γ′ ⦄ → SimpleHandlerεγ ε₀ γ₀ G
--              →  Prog ε γ A → Prog ε′ γ′ (G A)
--   handleεγ₀ h = hcata
--     (return ∘ ret h)
--     [ hcall h , call ]
--     [ henter h
--     , (λ op′ sc′ k′ → enter op′ sc′ (weave h k′)) ] ∘ to-frontε ∘ to-frontγ
-- 
--   hCatch  :  SimpleHandlerεγ Throw Catch Maybe
--   ret     hCatch x = just x
--   hcall   hCatch throw k = return nothing
--   henter  hCatch catch sc k = let m₁ = sc true; m₂ = sc false in
--     m₁ >>= maybe k (m₂ >>= maybe k (return nothing))
--   weave   hCatch k = maybe k (return nothing)
-- 
--   record ParameterizedAlgebraicHandler  (ε : Effect)
--                                         (P : Set) (G : Set → Set) : Set₁ where
--     field
--       ret    : A → P → G A
--       hcall  : (op : Op ε) → (Ret ε op → P → Prog ε′ γ′ (G X)) → P → Prog ε′ γ′ (G X)
--       weave  : (B′ → P → Prog ε′ γ′ (G X)) → G B′ → P → Prog ε′ γ′ (G X)
-- 
--   open ParameterizedAlgebraicHandler
-- 
--   handleε  :  ⦃ w : ε ∼ ε₀ ▸ ε′ ⦄
--            →  ParameterizedAlgebraicHandler ε₀ P G
--            →  Prog ε γ A → P → Prog ε′ γ (G A)
--   handleε h = hcata
--     (λ p → return ∘ ret h p)
--     [ hcall h , (λ op′ k′ → call op′ ∘ flip k′) ]
--     (λ op sc k p → enter op (flip sc p) (flip (weave h k) p))
--     ∘ to-frontε
-- 
--   hStateˢᶜ  :  ⦃ w : ε ∼ State ▸ ε′ ⦄
--             →  ParameterizedAlgebraicHandler State ℕ (_× ℕ)
--   ret    hStateˢᶜ x n           = x , n
--   hcall  hStateˢᶜ (put m)  k n  = k tt m
--   hcall  hStateˢᶜ get      k n  = k n n
--   weave  hStateˢᶜ k (x , m) _   = k x m
-- 
--   record LambdaM (V : Set) (M : Set → Set) : Set₁ where
--     field  lam : (V → M V)  → M V
--            app : V → M V    → M V
