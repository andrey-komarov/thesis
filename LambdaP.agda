module LambdaP where

open import OXIj.BrutalDepTypes
open Data-Vec
open Data-Any
open ≡-Prop
open ℕ-Op

module TransReflClosure where
  -- Transitive reflexive closure of a relation
  data _✴ {A} (R : A → A → Set) : A → A → Set where
    ε  : {a : A} → (R ✴) a a -- Reflexivity
    _∷✴_ : {a b c : A} → R a b → (R ✴) b c → (R ✴) a c
  -- Structurally ─ a list with two indexes, where each cons
  -- connects them by relation R.

  -- Transitivity
  _++✴_ : ∀ {A} {R : A → A → Set} {a b c} → (R ✴) a b → (R ✴) b c → (R ✴) a c
  ε ++✴ bs = bs
  (a ∷✴ as) ++✴ bs = a ∷✴ (as ++✴ bs)

  -- Closure of a closure is simply a closure
  concat✴ : ∀ {A} {R : A → A → Set} {x y} → ((R ✴) ✴) x y → (R ✴) x y
  concat✴ ε = ε
  concat✴ (y' ∷✴ y0) = y' ++✴ concat✴ y0

  -- General map between closures
  -- Comprehensible when (u ≡ id).
  map✴ : ∀ {A B} {R : A → A → Set} {S : B → B → Set} (u : A → B)
       → (∀ {x y} → R x y → S (u x) (u y))
       → ∀ {x y} → (R ✴) x y → (S ✴) (u x) (u y)
  map✴ u f ε = ε
  map✴ u f (y ∷✴ y') = f y ∷✴ map✴ u f y'

open TransReflClosure public

module Fin where
  data Fin : ℕ → Set where
    fzero : {n : ℕ} → Fin (succ n)
    fsucc : {n : ℕ} → Fin n → Fin (succ n)

  fpred : ∀ {n} (a b : Fin n) → ¬ (a ≡ b) → ¬ (fsucc a ≡ fsucc b)
  fpred fzero fzero ¬a≡b fa≡fb = ¬a≡b refl
  fpred fzero (fsucc b) ¬a≡b ()
  fpred (fsucc a) fzero ¬a≡b ()
  fpred (fsucc .b) (fsucc b) ¬a≡b refl = ¬a≡b refl

  _≡?_ : ∀ {n} → (a b : Fin n) → Dec (a ≡ b)
  fzero ≡? fzero = yes refl
  fzero ≡? fsucc b = no (λ ())
  fsucc a ≡? fzero = no (λ ())
  fsucc a ≡? fsucc b with a ≡? b
  fsucc .b ≡? fsucc b | yes refl = yes refl
  ... | no ¬≡ = no (fpred a b ¬≡)

--  cmp : ∀ {n} → (a b : Fin n) → Tri

open Fin

module LambdaPCalculusAtomicallyTypedWith (T : Set) where

  mutual
    data Term (n m : ℕ) : Set where
      ⋆_ : Fin n → Term n m
      λ⟨_⟩ : (τ : Type n m) → (N : Term (succ n) m) → Term n m
      _∙_ : Term n m → Term n m → Term n m
    
    data Type (n m : ℕ) : Set where
      ✶_ : Fin m → Type n m
      ∀⟨_⟩ : (τ : Type n m) → (γ : Type (succ n) m) → Type n m
      _◆_ : Type n m → Term n m → Type n m

    data Kind (n m : ℕ) : Set where
      ★ : Kind n m
      Π⟨_⟩ : (τ : Type n m) → (κ : Kind (succ n) m) → Kind n m

{-  Sub : (n m : ℕ) → Set
  Sub n m = (Fin n → Term m) × (Fin n → Type m)

  mutual
    T-sub : ∀ {n m} → (T : Term n) → (s : Sub n m) → Term m
    T-sub (⋆ x) (sT , sτ) = sT x
    T-sub (λ⟨ τ ⟩ T) s = λ⟨ {!!} ⟩ (T-sub T {!s!})
    T-sub (T₁ ∙ T₂) (sT , sτ) = {!!}

    τ-sub : ∀ {n m} → (τ : Type n) → (s : Sub n m) → Type m
    τ-sub τ s = {!!}

    κ-sub : ∀ {n m} → (κ : Kind n) → (s : Sub n m) → Kind m
    κ-sub κ s = {!!}
-}

  {- mutual
    T-sh1 : ∀ {n} → Term n → Term (succ n)
    T-sh1 (⋆ x) = ⋆ fsucc x
    T-sh1 (λ⟨ τ ⟩ T) = λ⟨ τ-sh1 τ ⟩ (T-sh1 T)
    T-sh1 (T₁ ∙ T₂) = T-sh1 T₁ ∙ T-sh1 T₂

    τ-sh1 : ∀ {n} → Type n → Type (succ n)
    τ-sh1 (✴ x) = ✴ fsucc x
    τ-sh1 (∀⟨ τ ⟩ γ) = ∀⟨ τ-sh1 τ ⟩ (τ-sh1 γ)
    τ-sh1 (τ ◆ x) = τ-sh1 τ ◆ T-sh1 x

    κ-sh1 : ∀ {n} → Kind n → Kind (succ n)
    κ-sh1 ★ = ★
    κ-sh1 (Π⟨ τ ⟩ κ) = Π⟨ τ-sh1 τ ⟩ (κ-sh1 κ)
    
  
  skip : ∀ {n m} → Sub n m → Sub (succ n) (succ m)
  skip s fzero = ⋆ fzero
  skip s (fsucc x) = T-sh1 (s x)

  mutual
    T-sub : ∀ {n m} → (T : Term n) → (s : Sub n m) → Term m
    T-sub (⋆ x) s = s x
    T-sub (λ⟨ τ ⟩ T) s = λ⟨ τ-sub τ s ⟩ (T-sub T (skip s))
    T-sub (T₁ ∙ T₂) s = T-sub T₁ s ∙ T-sub T₂ s

    τ-sub : ∀ {n m} → (τ : Type n) → (s : Sub n m) → Type m
    -- Опять этот гадкий случай. Видимо, ничего с этим
    -- не сделать и в well-typed подстановке сюда
    -- никто никогда не зайдёт
    τ-sub (✴ x) s = ✴ {!!}
    τ-sub (∀⟨ τ ⟩ γ) s = ∀⟨ τ-sub τ s ⟩ (τ-sub γ (skip s))
    τ-sub (τ ◆ x) s = τ-sub τ s ◆ T-sub x s

    κ-sub : ∀ {n m} → (κ : Kind n) → (s : Sub n m) → Kind m
    κ-sub ★ s = ★
    κ-sub (Π⟨ τ ⟩ κ) s = Π⟨ τ-sub τ s ⟩ (κ-sub κ (skip s))

{-  [_↦_] : ∀ {n} → Fin (succ n) → Term n → Sub (succ n) n
  -- Тут надо сравнить x и y и от этого плясать.
  -- Пока будет достаточно sub1
  [ x ↦ N ] y with x ≡? y
  [ x ↦ N ] .x | yes refl = N
  [ x ↦ N ] y | no ¬a = {!!}
-}

  sub1 : ∀ {n} → Term n → Sub (succ n) n
  sub1 N fzero = N
  sub1 N (fsucc x) = ⋆ x

  mutual

    data _→β_ {n : ℕ} : Term n → Term n → Set where
      here : ∀ {N M}{τ} → (λ⟨ τ ⟩ M ∙ N) →β T-sub M (sub1 N)
      in-λ⟨τ⟩ : ∀ {N}{τ₁ τ₂} → τ₁ →βₜ τ₂ → (λ⟨ τ₁ ⟩ N) →β (λ⟨ τ₂ ⟩ N)
      in-λ : ∀ {N₁ N₂}{τ} → N₁ →β N₂ → (λ⟨ τ ⟩ N₁) →β (λ⟨ τ ⟩ N₂)
      in-∙-L : ∀ {N₁ N₂}{M} → N₁ →β N₂ → (N₁ ∙ M) →β (N₂ ∙ M)
      in-∙-R : ∀ {N}{M₁ M₂} → M₁ →β M₂ → (N ∙ M₁) →β (N ∙ M₂)

    data _→βₜ_ {n : ℕ} : Type n → Type n → Set where
      in-∀-1 : ∀ {τ₁ τ₂}{σ} → τ₁ →βₜ τ₂ → (∀⟨ τ₁ ⟩ σ) →βₜ (∀⟨ τ₂ ⟩ σ)
      in-∀-2 : ∀ {τ}{σ₁ σ₂} → σ₁ →βₜ σ₂ → (∀⟨ τ ⟩ σ₁) →βₜ (∀⟨ τ ⟩ σ₂)
      in-◆-τ : ∀ {φ₁ φ₂}{M} → φ₁ →βₜ φ₂ → (φ₁ ◆ M) →βₜ (φ₂ ◆ M)
      in-◆-T : ∀ {φ}{M₁ M₂} → M₁ →β M₂ → (φ ◆ M₁) →βₜ (φ ◆ M₂)

    data _→βₖ_ {n : ℕ} : Kind n → Kind n → Set where
      in-Π-τ : ∀ {τ₁ τ₂}{κ} → τ₁ →βₜ τ₂ → (Π⟨ τ₁ ⟩ κ) →βₖ (Π⟨ τ₂ ⟩ κ)
      in-Π-κ : ∀ {τ}{κ₁ κ₂} → κ₁ →βₖ κ₂ → (Π⟨ τ ⟩ κ₁) →βₖ (Π⟨ τ ⟩ κ₂)

  _→'_ : ∀ {n} → Type n → Type n → Type n
  τ →' γ = ∀⟨ τ ⟩ (τ-sh1 γ)

  _⇒_ : ∀ {n} → Type n → Kind n → Kind n
  τ ⇒ κ = Π⟨ τ ⟩ (κ-sh1 κ)

  _→β✴_ : ∀ {n} → Term n → Term n → Set
  _→β✴_ = _→β_ ✴
  
  _→βₜ✴_ : ∀ {n} → Type n → Type n → Set
  _→βₜ✴_ = _→βₜ_ ✴

  _→βₖ✴_ : ∀ {n} → Kind n → Kind n → Set
  _→βₖ✴_ = _→βₖ_ ✴

  _≡β_ : ∀ {n} → Term n → Term n → Set
  _≡β_ {n} N M = Σ (Term n) (λ K → (N →β✴ K) ∧ (M →β✴ K))

  _≡βₜ_ : ∀ {n} → Type n → Type n → Set
  _≡βₜ_ {n} τ γ = Σ (Type n) (λ σ → (τ →βₜ✴ σ) ∧ (γ →βₜ✴ σ))

  _≡βₖ_ : ∀ {n} → Kind n → Kind n → Set
  _≡βₖ_ {n} κ₁ κ₂ = Σ (Kind n) (λ κ₃ → (κ₁ →βₖ✴ κ₃) ∧ (κ₂ →βₖ✴ κ₃))

  infixr 10 _∷τ_ _∷κ_
  data Ctx : (n : ℕ) → Set where
    ⟦⟧ : Ctx zero
    _∷τ_ : ∀ {n} → Type n → Ctx n → Ctx (succ n)
    _∷κ_ : ∀ {n} → Kind n → Ctx n → Ctx (succ n)

  mutual

    data _⊢_:□ : {n : ℕ} → Ctx n → Kind n → Set where
      _⊢★:□ : {n : ℕ} → (Γ : Ctx n) → Γ ⊢ ★ :□
      _⊢Π_:□ : ∀ {n τ κ}{Γ : Ctx n} 
        → ((τ ∷τ Γ) ⊢ κ :□) 
        → Γ ⊢ Π⟨ τ ⟩ κ :□
      κ-wk-1 : ∀ {n}{τ}{κ}{Γ : Ctx n}
        → Γ ⊢ τ :κ ★
        → Γ ⊢ κ :□
        → (τ ∷τ Γ) ⊢ κ-sh1 κ :□
      κ-wk-2 : ∀ {n}{κ}{κ'}{Γ : Ctx n}
        → Γ ⊢ κ :□
        → Γ ⊢ κ' :□
        → (κ ∷κ Γ) ⊢ κ-sh1 κ' :□
      
      

    data _⊢_:κ_ : {n : ℕ} → Ctx n → Type n → Kind n → Set where
      τ-1 : ∀ {n}{κ}{Γ : Ctx n} 
        → Γ ⊢ κ :□ 
        → ((κ ∷κ Γ) ⊢ (✴ fzero) :κ (κ-sh1 κ))
      τ-2 : ∀ {n}{φ}{τ}{κ}{M}{Γ : Ctx n}
        → Γ ⊢ φ :κ Π⟨ τ ⟩ κ
        → Γ ⊢ M :τ τ
        → Γ ⊢ φ ◆ M :κ κ-sub κ {- [ fzero ↦ M ] -} (sub1 M)
      τ-3 : ∀ {n}{τ}{σ}{Γ : Ctx n}
        → ((τ ∷τ Γ) ⊢ σ :κ ★) 
        → Γ ⊢ ∀⟨ τ ⟩ σ :κ ★
      τ-wk-1 : ∀ {n}{τ}{φ}{κ}{Γ : Ctx n}
        → Γ ⊢ τ :κ ★
        → Γ ⊢ φ :κ κ
        → (τ ∷τ Γ) ⊢ τ-sh1 φ :κ κ-sh1 κ
      τ-wk-2 : ∀ {n}{κ}{φ}{κ'}{Γ : Ctx n}
        → Γ ⊢ κ :□
        → Γ ⊢ φ :κ κ'
        → (κ ∷κ Γ) ⊢ τ-sh1 φ :κ κ-sh1 κ'
      τ-conv : ∀ {n}{φ}{κ}{κ'}{Γ : Ctx n}
        → Γ ⊢ φ :κ κ
        → κ ≡βₖ κ'
        → Γ ⊢ φ :κ κ'
  
    data _⊢_:τ_ : {n : ℕ} → Ctx n → Term n → Type n → Set where
      T-1 : ∀ {n}{τ}{Γ : Ctx n}
        → Γ ⊢ τ :κ ★
        → (τ ∷τ Γ) ⊢ ⋆ fzero :τ τ-sh1 τ
      T-2 : ∀ {n}{τ}{σ}{N}{M}{Γ : Ctx n}
        → Γ ⊢ N :τ ∀⟨ τ ⟩ σ
        → Γ ⊢ M :τ τ
        → Γ ⊢ N ∙ M :τ τ-sub σ {- [ fzero ↦ M ] -} (sub1 M)
      T-3 : ∀ {n}{τ}{M}{σ}{Γ : Ctx n}
        → (τ ∷τ Γ) ⊢ M :τ σ
        → Γ ⊢ λ⟨ τ ⟩ M :τ ∀⟨ τ ⟩ σ
      T-wk-1 : ∀ {n}{τ}{M}{σ}{Γ : Ctx n}
        → Γ ⊢ τ :κ ★
        → Γ ⊢ M :τ σ
        → (τ ∷τ Γ) ⊢ T-sh1 M :τ τ-sh1 σ
      T-wk-2 : ∀ {n}{κ}{M}{σ}{Γ : Ctx n}
        → Γ ⊢ κ :□
        → Γ ⊢ M :τ σ
        → (κ ∷κ Γ) ⊢ T-sh1 M :τ τ-sh1 σ
      T-conv : ∀ {n}{M}{σ₁}{σ₂}{Γ : Ctx n}
        → Γ ⊢ M :τ σ₁
        → σ₁ ≡βₜ σ₂
        → Γ ⊢ M :τ σ₂

-}
