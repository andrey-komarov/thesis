module VCS3 where

open import OXIj.BrutalDepTypes

module Data-Maybe where

  data _⁇ (A : Set) : Set where
    ø : A ⁇
    ⊙ : (a : A) → A ⁇
    
  map⁇ : ∀ {A B : Set} → (f : A → B) → A ⁇ → B ⁇
  map⁇ f ø = ø
  map⁇ f (⊙ a) = ⊙ (f a)
  
  maybe : ∀ {A B : Set} → B → (A → B) → A ⁇ → B
  maybe b f ø = b
  maybe b f (⊙ a) = f a

module With-⋀-and-⋙ (A : Set) where

  open Data-Vec
  open ≡-Prop

  Form : ℕ → Set
  Form = Vec Bool 
  
  data Patch : ∀ {n} → Form n → Set where
    O : Patch []
    ⊥∷ : ∀ {n}{f : Form n} → Patch f → Patch (false ∷ f)
    ⟨_⇒_⟩∷_ : ∀ {n}{f : Form n}
      → (from to : A)
      → Patch f → Patch (true ∷ f)

  data _∥_ : ∀ {n} → Form n → Form n → Set where
    []∥[] : [] ∥ []
    ⊥∥⊥ : ∀ {n}{f₁ f₂ : Form n} → f₁ ∥ f₂ → (false ∷ f₁) ∥ (false ∷ f₂)
    ⊤∥⊥ : ∀ {n}{f₁ f₂ : Form n} → f₁ ∥ f₂ → (true ∷ f₁) ∥ (false ∷ f₂)
    ⊥∥⊤ : ∀ {n}{f₁ f₂ : Form n} → f₁ ∥ f₂ → (false ∷ f₁) ∥ (true ∷ f₂)
    
  data _⊂_ : ∀ {n} → Form n → Form n → Set where
    []⊂[] : [] ⊂ []
    ⊂⊤ : ∀ {n}{f₁ f₂ : Form n} → (b : Bool) → (b ∷ f₁) ⊂ (true ∷ f₂)
    ⊥⊂⊥ : ∀ {n}{f₁ f₂ : Form n} → (false ∷ f₁) ⊂ (false ∷ f₂)
    
  data _⋙?_ : ∀ {n}{f₁ f₂ : Form n} → Patch f₁ → Patch f₂ → Set where
    O⋙?O : O ⋙? O
    ⊥⋙?⊥ : ∀ {n}{f₁ f₂ : Form n} {p₁ : Patch f₁} {p₂ : Patch f₂}
      → (p₁⋙?p₂ : p₁ ⋙? p₂) → (⊥∷ p₁) ⋙? (⊥∷ p₂)
    ⊤⋙?⊥ : ∀ {n}{f₁ f₂ : Form n} {p₁ : Patch f₁} {p₂ : Patch f₂}
      → (from to : A) → (p₁⋙?p₂ : p₁ ⋙? p₂)
      → (⟨ from ⇒ to ⟩∷ p₁) ⋙? (⊥∷ p₂)
    ⊤⋙?⊤ : ∀ {n}{f₁ f₂ : Form n} {p₁ : Patch f₁} {p₂ : Patch f₂}
      → (from to to₂ : A) → (p₁⋙?p₂ : p₁ ⋙? p₂)
      → (⟨ from ⇒ to ⟩∷ p₁) ⋙? (⟨ to ⇒ to₂ ⟩∷ p₂)
    
  data _⊏_ : ∀ {n}{f : Form n} → Patch f → Vec A n → Set where
    []⊏[] : O ⊏ []
    ⊥⊏ : ∀ {n}{f : Form n}{p : Patch f}{v : Vec A n}
      → (a : A) → p ⊏ v → (⊥∷ p) ⊏ (a ∷ v)
    ⊤⊏ : ∀ {n}{f : Form n}{p : Patch f}{v : Vec A n}
      → (a b : A)
      → p ⊏ v → (⟨ a ⇒ b ⟩∷ p) ⊏ (a ∷ v)

  patch : ∀ {n}{f : Form n} → (p : Patch f) → (x : Vec A n) → p ⊏ x → Vec A n
  patch O [] []⊏[] = []
  patch (⊥∷ p) (x ∷ xs) (⊥⊏ .x p⊏xs) = x ∷ patch p xs p⊏xs
  patch (⟨ .f ⇒ t ⟩∷ p) (f ∷ xs) (⊤⊏ .f .t p⊏xs) = 
    t ∷ patch p xs p⊏xs
  
  _∧ₛ_ : ∀ {n} (f₁ f₂ : Form n) → f₁ ∥ f₂ → Form n
  _∧ₛ_ [] [] []∥[] = []
  _∧ₛ_ (.false ∷ xs) (.false ∷ ys) (⊥∥⊥ p) = false ∷ (xs ∧ₛ ys) p
  _∧ₛ_ (.true ∷ xs) (.false ∷ ys) (⊤∥⊥ p) = true ∷ (xs ∧ₛ ys) p
  _∧ₛ_ (.false ∷ xs) (.true ∷ ys) (⊥∥⊤ p) = true ∷ (xs ∧ₛ ys) p

  unite : ∀ {n} {f₁ f₂ : Form n} → f₁ ∥ f₂ → Form n
  unite {n} {f₁} {f₂} p = (f₁ ∧ₛ f₂) p

  _∧ₚ_ : ∀ {n} {f₁ f₂ : Form n} (p₁ : Patch f₁) (p₂ : Patch f₂)
    → (f₁∥f₂ : f₁ ∥ f₂) → Patch (unite f₁∥f₂)    
  _∧ₚ_ O O []∥[] = O
  _∧ₚ_ (⊥∷ p₁) (⊥∷ p₂) (⊥∥⊥ f₁∥f₂) = ⊥∷ ((p₁ ∧ₚ p₂) f₁∥f₂)
  _∧ₚ_ (⊥∷ p₁) (⟨ from ⇒ to ⟩∷ p₂) (⊥∥⊤ f₁∥f₂) = 
    ⟨ from ⇒ to ⟩∷ (p₁ ∧ₚ p₂) f₁∥f₂
  _∧ₚ_ (⟨ from ⇒ to ⟩∷ p₁) (⊥∷ p₂) (⊤∥⊥ f₁∥f₂) = 
    ⟨ from ⇒ to ⟩∷ (p₁ ∧ₚ p₂) f₁∥f₂
    
  _⋙ₚ_ : ∀ {n} {f₁ f₂ : Form n} (p₁ : Patch f₁) (p₂ : Patch f₂)
    → (p₁ ⋙? p₂) → Patch f₁
  _⋙ₚ_ O O O⋙?O = O
  _⋙ₚ_ (⊥∷ p₁) (⊥∷ p₂) (⊥⋙?⊥ p₁⋙?p₂) = ⊥∷ ((p₁ ⋙ₚ p₂) p₁⋙?p₂)
  _⋙ₚ_ (⟨ from ⇒ to ⟩∷ p₁) (⊥∷ p₂) (⊤⋙?⊥ .from .to p₁⋙?p₂) = 
    ⟨ from ⇒ to ⟩∷ ((p₁ ⋙ₚ p₂) p₁⋙?p₂)
  _⋙ₚ_ (⟨ from ⇒ .from₁ ⟩∷ p₁) (⟨ from₁ ⇒ to₁ ⟩∷ p₂) (⊤⋙?⊤ .from .from₁ .to₁ p₁⋙?p₂) = 
    ⟨ from₁ ⇒ to₁ ⟩∷ ((p₁ ⋙ₚ p₂) p₁⋙?p₂)

  {- p₁ ⟷ p₂ ─ p₁ операционно эквивалентен p₂ -}
  {- Это определение прохое. 
     "Патчи эквивалентны, если _на общей области определения_ дают
       одинаковые результаты."
     Области опеределения не пересекаются ⇒ можно творить какую
       угодно фигню и считаться эквивалентными.
  -}
  _⟷_ : ∀ {n}{f₁ f₂ : Form n} 
    → (p₁ : Patch f₁) → (p₂ : Patch f₂) → Set
  _⟷_ {n} p₁ p₂ = ∀ (x : Vec A n) → (p₁⊏x : p₁ ⊏ x) → (p₂⊏x : p₂ ⊏ x) 
    → patch p₁ x p₁⊏x ≡ patch p₂ x p₂⊏x
    
  vec-strip : ∀ {n} {a₁ a₂ : A} {ax₁ ax₂ : Vec A n}
    → (a₁ ∷ ax₁) ≡ (a₂ ∷ ax₂) → ax₁ ≡ ax₂
  vec-strip refl = refl
  
  vec-prepend : ∀ {n} {ax₁ ax₂ : Vec A n}
    → (a : A) → ax₁ ≡ ax₂ → (a ∷ ax₁) ≡ (a ∷ ax₂)
  vec-prepend _ refl = refl
  
  strip-⊥⊥ : ∀ {n} {f₁ f₂ : Form n} {p₁ : Patch f₁} {p₂ : Patch f₂}
    → (x : A) → (⊥∷ p₁) ⟷ (⊥∷ p₂) → p₁ ⟷ p₂
  strip-⊥⊥ x ⊥∷p₁⟷⊥∷p₂ xs p₁⊏xs p₂⊏xs = vec-strip (⊥∷p₁⟷⊥∷p₂ (x ∷ xs) (⊥⊏ x p₁⊏xs) (⊥⊏ x p₂⊏xs))
  
  patch-lem-1 : ∀ {n} {f₁ f₂ : Form n} {p₁ : Patch f₁} {p₂ : Patch f₂} {x t₁ t₂ : A}
    → (⟨ x ⇒ t₁ ⟩∷ p₁) ⟷ (⟨ x ⇒ t₂ ⟩∷ p₂) → t₁ ≡ t₂
  patch-lem-1 {x = x}{t₁}{t₂} 1⟷2 = {!1⟷2 (x ∷ ?)!}
  
  -- c = c' ∧ c'' ⇒ (a ∧ b) ⋙ c ⟷ (a ⋙ c') ∧ (b ⋙ c'')
  {- Плохая формулировка. `c` взято не так, как надо. 
     Надо брать `c :≡ c' ∧ c''`, а не ∀ c . c ⟷ c' ∧ c''
  -}
  {-
  ∧-⋙-lem : ∀ {n} {fᵃ fᵇ fᶜ' fᶜ'' : Form n}
    (c' : Patch fᶜ')(c'' : Patch fᶜ'')
    (a : Patch fᵃ)(b : Patch fᵇ)
    (c'∥c'' : fᶜ' ∥ fᶜ'') 
    (c : Patch (unite c'∥c''))
    (c=c'∧c'' : c ⟷ ((c' ∧ₚ c'') c'∥c''))
    (a∥b : fᵃ ∥ fᵇ)
    (a∧b⋙?c : (a ∧ₚ b) a∥b ⋙? c)
    (a⋙?c' : a ⋙? c')
    (b⋙?c'' : b ⋙? c'')
    → (((a ∧ₚ b) a∥b) ⋙ₚ c) a∧b⋙?c 
      ⟷ ((a ⋙ₚ c') a⋙?c' ∧ₚ (b ⋙ₚ c'') b⋙?c'') a∥b
  ∧-⋙-lem O O O O []∥[] .O c=c'∧c'' []∥[] O⋙?O O⋙?O O⋙?O [] []⊏[] []⊏[] = refl
  ∧-⋙-lem (⊥∷ c') (⊥∷ c'') (⊥∷ a) (⊥∷ b) (⊥∥⊥ c'∥c'') (⊥∷ c) c=c'∧c'' (⊥∥⊥ a∥b) (⊥⋙?⊥ a∧b⋙?c) (⊥⋙?⊥ a⋙?c') (⊥⋙?⊥ b⋙c'') (x ∷ x₁) (⊥⊏ .x a∧b⋙c⊏x) (⊥⊏ .x a⋙c'∧b⋙c''⊏x) 
    = vec-prepend x (∧-⋙-lem c' c'' a b c'∥c'' c (strip-⊥⊥ x c=c'∧c'') a∥b a∧b⋙?c a⋙?c' b⋙c'' x₁ a∧b⋙c⊏x a⋙c'∧b⋙c''⊏x)
  ∧-⋙-lem (⊥∷ c') (⊥∷ c'') (⊥∷ a) (⟨ .x ⇒ to ⟩∷ b) (⊥∥⊥ c'∥c'') (⊥∷ c) c=c'∧c'' (⊥∥⊤ a∥b) (⊤⋙?⊥ .x .to a∧b⋙?c) (⊥⋙?⊥ a⋙?c') (⊤⋙?⊥ .x .to b⋙c'') (x ∷ x₁) (⊤⊏ .x .to a∧b⋙c⊏x) (⊤⊏ .x .to a⋙c'∧b⋙c''⊏x) 
    = vec-prepend to (∧-⋙-lem c' c'' a b c'∥c'' c (strip-⊥⊥ x c=c'∧c'') a∥b a∧b⋙?c a⋙?c' b⋙c'' x₁ a∧b⋙c⊏x a⋙c'∧b⋙c''⊏x)
  ∧-⋙-lem (⊥∷ c') (⊥∷ c'') (⟨ .x ⇒ to ⟩∷ a) (⊥∷ b) (⊥∥⊥ c'∥c'') (⊥∷ c) c=c'∧c'' (⊤∥⊥ a∥b) (⊤⋙?⊥ .x .to a∧b⋙?c) (⊤⋙?⊥ .x .to a⋙?c') (⊥⋙?⊥ b⋙c'') (x ∷ x₁) (⊤⊏ .x .to a∧b⋙c⊏x) (⊤⊏ .x .to a⋙c'∧b⋙c''⊏x) 
    = vec-prepend to (∧-⋙-lem c' c'' a b c'∥c'' c (strip-⊥⊥ x c=c'∧c'') a∥b a∧b⋙?c a⋙?c' b⋙c'' x₁ a∧b⋙c⊏x a⋙c'∧b⋙c''⊏x)
  ∧-⋙-lem (⊥∷ c') (⟨ from ⇒ to ⟩∷ c'') (⊥∷ a) (⊥∷ b) (⊥∥⊤ c'∥c'') c c=c'∧c'' (⊥∥⊥ a∥b) a∧b⋙?c a⋙?c' () x a∧b⋙c⊏x a⋙c'∧b⋙c''⊏x
  ∧-⋙-lem (⊥∷ c') (⟨ .x ⇒ to ⟩∷ c'') (⊥∷ a) (⟨ from₁ ⇒ .x ⟩∷ b) (⊥∥⊤ c'∥c'') (⟨ .x ⇒ .to₂ ⟩∷ p₂) c=c'∧c'' (⊥∥⊤ a∥b) (⊤⋙?⊤ .from₁ .x to₂ a∧b⋙?c) (⊥⋙?⊥ a⋙?c') (⊤⋙?⊤ .from₁ .x .to b⋙c'') (x ∷ x₁) (⊤⊏ .x .to₂ a∧b⋙c⊏x) (⊤⊏ .x .to a⋙c'∧b⋙c''⊏x) 
    = {!!}
  ∧-⋙-lem (⊥∷ c') (⟨ from ⇒ to ⟩∷ c'') (⟨ from₁ ⇒ to₁ ⟩∷ a) (⊥∷ b) c'∥c'' c c=c'∧c'' a∥b a∧b⋙?c a⋙?c' b⋙c'' x a∧b⋙c⊏x a⋙c'∧b⋙c''⊏x = {!!}
  ∧-⋙-lem (⊥∷ c') (⟨ from ⇒ to ⟩∷ c'') (⟨ from₁ ⇒ to₁ ⟩∷ a) (⟨ from₂ ⇒ to₂ ⟩∷ b) c'∥c'' c c=c'∧c'' a∥b a∧b⋙?c a⋙?c' b⋙c'' x a∧b⋙c⊏x a⋙c'∧b⋙c''⊏x = {!!}
  ∧-⋙-lem (⟨ from ⇒ to ⟩∷ c') (⊥∷ c'') (⊥∷ a) (⊥∷ b) c'∥c'' c c=c'∧c'' a∥b a∧b⋙?c a⋙?c' b⋙c'' x a∧b⋙c⊏x a⋙c'∧b⋙c''⊏x = {!!}
  ∧-⋙-lem (⟨ from ⇒ to ⟩∷ c') (⊥∷ c'') (⊥∷ a) (⟨ from₁ ⇒ to₁ ⟩∷ b) c'∥c'' c c=c'∧c'' a∥b a∧b⋙?c a⋙?c' b⋙c'' x a∧b⋙c⊏x a⋙c'∧b⋙c''⊏x = {!!}
  ∧-⋙-lem (⟨ from ⇒ to ⟩∷ c') (⊥∷ c'') (⟨ from₁ ⇒ to₁ ⟩∷ a) (⊥∷ b) c'∥c'' c c=c'∧c'' a∥b a∧b⋙?c a⋙?c' b⋙c'' x a∧b⋙c⊏x a⋙c'∧b⋙c''⊏x = {!!}
  ∧-⋙-lem (⟨ from ⇒ to ⟩∷ c') (⊥∷ c'') (⟨ from₁ ⇒ to₁ ⟩∷ a) (⟨ from₂ ⇒ to₂ ⟩∷ b) c'∥c'' c c=c'∧c'' a∥b a∧b⋙?c a⋙?c' b⋙c'' x a∧b⋙c⊏x a⋙c'∧b⋙c''⊏x = {!!}
  ∧-⋙-lem (⟨ from ⇒ to ⟩∷ c') (⟨ from₁ ⇒ to₁ ⟩∷ c'') (⊥∷ a) (⊥∷ b) c'∥c'' c c=c'∧c'' a∥b a∧b⋙?c a⋙?c' b⋙c'' x a∧b⋙c⊏x a⋙c'∧b⋙c''⊏x = {!!}
  ∧-⋙-lem (⟨ from ⇒ to ⟩∷ c') (⟨ from₁ ⇒ to₁ ⟩∷ c'') (⊥∷ a) (⟨ from₂ ⇒ to₂ ⟩∷ b) c'∥c'' c c=c'∧c'' a∥b a∧b⋙?c a⋙?c' b⋙c'' x a∧b⋙c⊏x a⋙c'∧b⋙c''⊏x = {!!}
  ∧-⋙-lem (⟨ from ⇒ to ⟩∷ c') (⟨ from₁ ⇒ to₁ ⟩∷ c'') (⟨ from₂ ⇒ to₂ ⟩∷ a) (⊥∷ b) c'∥c'' c c=c'∧c'' a∥b a∧b⋙?c a⋙?c' b⋙c'' x a∧b⋙c⊏x a⋙c'∧b⋙c''⊏x = {!!}
  ∧-⋙-lem (⟨ from ⇒ to ⟩∷ c') (⟨ from₁ ⇒ to₁ ⟩∷ c'') (⟨ from₂ ⇒ to₂ ⟩∷ a) (⟨ from₃ ⇒ to₃ ⟩∷ b) c'∥c'' c c=c'∧c'' a∥b a∧b⋙?c a⋙?c' b⋙c'' x a∧b⋙c⊏x a⋙c'∧b⋙c''⊏x = {!!}
    -}

