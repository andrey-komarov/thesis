module VCS3 where

open import OXIj.BrutalDepTypes

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
    
  -- Доказательство того, что можно делать p₁ ⋙ p₂
  -- p₂ может менять только то, что менял p₁
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

  -- ещё и транзитивность фиг докажешь
  ⟷-trans : ∀ {n}{f₁ f₂ f₃ : Form n}
    → {p₁ : Patch f₁}{p₂ : Patch f₂}{p₃ : Patch f₃}
    → (p₁ ⟷ p₂) → (p₂ ⟷ p₃) → (p₁ ⟷ p₃)
  ⟷-trans p₁⟷p₂ p₂⟷p₃ x p₁⊏x p₃⊏x = {!!}
  
    
  -- Улучшим
  _⟶_ : ∀ {n}{f₁ f₂ : Form n}
    → (p₁ : Patch f₁) → (p₂ : Patch f₂) → Set
  _⟶_ {n} p₁ p₂ = ∀ (x : Vec A n) 
    → (p₁⊏x : p₁ ⊏ x) → Σ (p₂ ⊏ x) (λ p₂⊏x → 
      (patch p₁ x p₁⊏x ≡ patch p₂ x p₂⊏x))
      
      
  -- А это выглядит уже более лучше
  -- Ведут себя одинаково на общей области определения и области 
  -- определения совпадают

  -- UPD и доказывать приятней. Всегда нужно было сделать индукционный
  -- переход, после чего применить либо ⟶-prepend-⊥⊥, либо
  -- ⟶-prepend-⊤⊤ к результату
  _⟷₂_ : ∀ {n}{f₁ f₂ : Form n}
    → (p₁ : Patch f₁) → (p₂ : Patch f₂) → Set
  p₁ ⟷₂ p₂ = (p₁ ⟶ p₂) ∧ (p₂ ⟶ p₁)
    
  ⟷-bad : (a b c d : A) → (a ≠ b) → (⟨ a ⇒ c ⟩∷ O) ⟷ (⟨ b ⇒ d ⟩∷ O)
  ⟷-bad .x .x c d a≠b (x ∷ []) (⊤⊏ .x .c []⊏[]) (⊤⊏ .x .d []⊏[]) = 
    ⊥-elim (a≠b refl) 
    
  ⟶-trans : ∀ {n}{f₁ f₂ f₃ : Form n}
    → {p₁ : Patch f₁}{p₂ : Patch f₂}{p₃ : Patch f₃}
    → (p₁ ⟶ p₂) → (p₂ ⟶ p₃) → (p₁ ⟶ p₃)
  ⟶-trans {p₁ = p₁}{p₂}{p₃} p₁⟶p₂ p₂⟶p₃ x p₁⊏x 
    with patch p₁ x p₁⊏x | p₁⟶p₂ x p₁⊏x
  ... | .(patch p₂ x p₂⊏x) | p₂⊏x , refl = p₂⟶p₃ x p₂⊏x

  ⟷₂-trans : ∀ {n}{f₁ f₂ f₃ : Form n}
    → {p₁ : Patch f₁}{p₂ : Patch f₂}{p₃ : Patch f₃}
    → (p₁ ⟷₂ p₂) → (p₂ ⟷₂ p₃) → (p₁ ⟷₂ p₃)
  ⟷₂-trans (p₁⟶p₂ , p₂⟶p₁) (p₂⟶p₃ , p₃⟶p₂) = 
    (⟶-trans p₁⟶p₂ p₂⟶p₃) , (⟶-trans p₃⟶p₂ p₂⟶p₁)
    
  ⟶-prepend-⊥⊥ : ∀ {n}{f₁ f₂ : Form n}
    → {p₁ : Patch f₁} → {p₂ : Patch f₂}
    → (p₁ ⟶ p₂) → (⊥∷ p₁ ⟶ ⊥∷ p₂)
  ⟶-prepend-⊥⊥ {p₁ = p₁}{p₂} p₁⟶p₂ (x ∷ xs) (⊥⊏ .x p₁⊏xs) 
    with patch p₁ xs p₁⊏xs | p₁⟶p₂ xs p₁⊏xs
  ... | .(patch p₂ xs p₂⊏xs) | p₂⊏xs , refl = (⊥⊏ x p₂⊏xs) , refl
  
  ⟶-prepend-⊤⊤ : ∀ {n}{f₁ f₂ : Form n}
    → {p₁ : Patch f₁} → {p₂ : Patch f₂}
    → (from to : A)
    → (p₁ ⟶ p₂) → (⟨ from ⇒ to ⟩∷ p₁ ⟶ ⟨ from ⇒ to ⟩∷ p₂)
  ⟶-prepend-⊤⊤ {p₁ = p₁}{p₂} .x to p₁⟷p₂ (x ∷ xs) (⊤⊏ .x .to p₁⊏xs) 
    with patch p₁ xs p₁⊏xs | p₁⟷p₂ xs p₁⊏xs 
  ... | .(patch p₂ xs p₂⊏xs) | p₂⊏xs , refl = ⊤⊏ x to p₂⊏xs , refl

    
  module ⟷₂-∧-lemmas where
    ∥-comm : ∀ {n}{f₁ f₂ : Form n} → f₁ ∥ f₂ → f₂ ∥ f₁
    ∥-comm []∥[] = []∥[]
    ∥-comm (⊥∥⊥ f₁∥f₂) = ⊥∥⊥ (∥-comm f₁∥f₂)
    ∥-comm (⊤∥⊥ f₁∥f₂) = ⊥∥⊤ (∥-comm f₁∥f₂)
    ∥-comm (⊥∥⊤ f₁∥f₂) = ⊤∥⊥ (∥-comm f₁∥f₂)

    lemma-∥-unite : ∀ {n}{f₁ f₂ f₃ : Form n} 
      → (f₁∥f₂ : f₁ ∥ f₂) → f₂ ∥ f₃ → f₁ ∥ f₃
      → unite f₁∥f₂ ∥ f₃
    lemma-∥-unite []∥[] []∥[] []∥[] = []∥[]
    lemma-∥-unite (⊥∥⊥ f₁∥f₂) (⊥∥⊥ f₂∥f₃) (⊥∥⊥ f₁∥f₃) = 
      ⊥∥⊥ (lemma-∥-unite f₁∥f₂ f₂∥f₃ f₁∥f₃)
    lemma-∥-unite (⊥∥⊥ f₁∥f₂) (⊥∥⊤ f₂∥f₃) (⊥∥⊤ f₁∥f₃) = 
      ⊥∥⊤ (lemma-∥-unite f₁∥f₂ f₂∥f₃ f₁∥f₃)
    lemma-∥-unite (⊤∥⊥ f₁∥f₂) (⊥∥⊥ f₂∥f₃) (⊤∥⊥ f₁∥f₃) = 
      ⊤∥⊥ (lemma-∥-unite f₁∥f₂ f₂∥f₃ f₁∥f₃)
    lemma-∥-unite (⊥∥⊤ f₁∥f₂) (⊤∥⊥ f₂∥f₃) (⊥∥⊥ f₁∥f₃) = 
      ⊤∥⊥ (lemma-∥-unite f₁∥f₂ f₂∥f₃ f₁∥f₃)
    
    ∧-comm : ∀ {n}{f₁ f₂ : Form n}
      → (f₁∥f₂ : f₁ ∥ f₂)
      → (p₁ : Patch f₁) → (p₂ : Patch f₂)
      → ((p₁ ∧ₚ p₂) f₁∥f₂) ⟷₂ ((p₂ ∧ₚ p₁) (∥-comm f₁∥f₂))
    ∧-comm []∥[] O O = (λ x x₁ → x₁ , refl) , (λ x x₁ → x₁ , refl)
    ∧-comm (⊥∥⊥ f₁∥f₂) (⊥∷ p₁) (⊥∷ p₂) =
      (⟶-prepend-⊥⊥ (fst p)) , (⟶-prepend-⊥⊥ (snd p)) where
      p = ∧-comm f₁∥f₂ p₁ p₂
    ∧-comm (⊤∥⊥ f₁∥f₂) (⟨ from ⇒ to ⟩∷ p₁) (⊥∷ p₂) =
      (⟶-prepend-⊤⊤ from to (fst p)) , (⟶-prepend-⊤⊤ from to (snd p)) where
      p = ∧-comm f₁∥f₂ p₁ p₂
    ∧-comm (⊥∥⊤ f₁∥f₂) (⊥∷ p₁) (⟨ from ⇒ to ⟩∷ p₂) = 
      (⟶-prepend-⊤⊤ from to (fst p)) , (⟶-prepend-⊤⊤ from to (snd p)) where
      p = ∧-comm f₁∥f₂ p₁ p₂
    
    ∧-trans : ∀ {n}{f₁ f₂ f₃ : Form n}
      → (f₁∥f₂ : f₁ ∥ f₂) → (f₂∥f₃ : f₂ ∥ f₃) → (f₁∥f₃ : f₁ ∥ f₃)
      → (p₁ : Patch f₁) → (p₂ : Patch f₂) → (p₃ : Patch f₃)
      → ((p₁ ∧ₚ p₂) f₁∥f₂ ∧ₚ p₃) (lemma-∥-unite f₁∥f₂ f₂∥f₃ f₁∥f₃)
        ⟷₂ 
        (p₁ ∧ₚ (p₂ ∧ₚ p₃) f₂∥f₃) 
          (∥-comm (lemma-∥-unite f₂∥f₃ (∥-comm f₁∥f₃) (∥-comm f₁∥f₂)))
    ∧-trans []∥[] []∥[] []∥[] O O O = (λ x x₁ → x₁ , refl) , (λ x x₁ → x₁ , refl)
    ∧-trans (⊥∥⊥ f₁∥f₂) (⊥∥⊥ f₂∥f₃) (⊥∥⊥ f₁∥f₃) (⊥∷ p₁) (⊥∷ p₂) (⊥∷ p₃) = 
      (⟶-prepend-⊥⊥ (fst p)) , (⟶-prepend-⊥⊥ (snd p)) where
      p = ∧-trans f₁∥f₂ f₂∥f₃ f₁∥f₃ p₁ p₂ p₃
    ∧-trans (⊥∥⊥ f₁∥f₂) (⊥∥⊤ f₂∥f₃) (⊥∥⊤ f₁∥f₃) (⊥∷ p₁) (⊥∷ p₂) (⟨ from ⇒ to ⟩∷ p₃) = 
      (⟶-prepend-⊤⊤ from to (fst p)) , (⟶-prepend-⊤⊤ from to (snd p)) where
      p = ∧-trans f₁∥f₂ f₂∥f₃ f₁∥f₃ p₁ p₂ p₃
    ∧-trans (⊤∥⊥ f₁∥f₂) (⊥∥⊥ f₂∥f₃) (⊤∥⊥ f₁∥f₃) (⟨ from ⇒ to ⟩∷ p₁) (⊥∷ p₂) (⊥∷ p₃) = 
      (⟶-prepend-⊤⊤ from to (fst p)) , (⟶-prepend-⊤⊤ from to (snd p)) where 
      p = ∧-trans f₁∥f₂ f₂∥f₃ f₁∥f₃ p₁ p₂ p₃
    ∧-trans (⊤∥⊥ f₁∥f₂) (⊥∥⊤ f₂∥f₃) () p₁ p₂ p₃
    ∧-trans (⊥∥⊤ f₁∥f₂) (⊤∥⊥ f₂∥f₃) (⊥∥⊥ f₁∥f₃) (⊥∷ p₁) (⟨ from ⇒ to ⟩∷ p₂) (⊥∷ p₃) = 
      (⟶-prepend-⊤⊤ from to (fst p)) , (⟶-prepend-⊤⊤ from to (snd p)) where 
      p = ∧-trans f₁∥f₂ f₂∥f₃ f₁∥f₃ p₁ p₂ p₃
      
  module ⟷₂-⋙-lemmas where
    
    ∧-⋙-lem : ∀ {n} {fᵃ fᵇ fᶜ' fᶜ'' : Form n}
      (c' : Patch fᶜ')(c'' : Patch fᶜ'')
      (a : Patch fᵃ)(b : Patch fᵇ)
      (c'∥c'' : fᶜ' ∥ fᶜ'') 
      (a∥b : fᵃ ∥ fᵇ)
      (a∧b⋙?c : (a ∧ₚ b) a∥b ⋙? ((c' ∧ₚ c'') c'∥c''))
      (a⋙?c' : a ⋙? c')
      (b⋙?c'' : b ⋙? c'')
      → (((a ∧ₚ b) a∥b) ⋙ₚ ((c' ∧ₚ c'') c'∥c'')) a∧b⋙?c 
        ⟷₂ ((a ⋙ₚ c') a⋙?c' ∧ₚ (b ⋙ₚ c'') b⋙?c'') a∥b
    ∧-⋙-lem O O O O []∥[] []∥[] O⋙?O O⋙?O O⋙?O = (λ x x₁ → x₁ , refl) , (λ x x₁ → x₁ , refl)
    ∧-⋙-lem (⊥∷ c') (⊥∷ c'') (⊥∷ a) (⊥∷ b) (⊥∥⊥ c'∥c'') (⊥∥⊥ a∥b) (⊥⋙?⊥ a∧b⋙?c) (⊥⋙?⊥ a⋙?c') (⊥⋙?⊥ b⋙c'') = 
      (⟶-prepend-⊥⊥ (fst p)) , (⟶-prepend-⊥⊥ (snd p)) where
      p = ∧-⋙-lem c' c'' a b c'∥c'' a∥b a∧b⋙?c a⋙?c' b⋙c''
    ∧-⋙-lem (⊥∷ c') (⊥∷ c'') (⊥∷ a) (⟨ from ⇒ to ⟩∷ b) (⊥∥⊥ c'∥c'') (⊥∥⊤ a∥b) (⊤⋙?⊥ .from .to a∧b⋙?c) (⊥⋙?⊥ a⋙?c') (⊤⋙?⊥ .from .to b⋙c'') = 
      (⟶-prepend-⊤⊤ from to (fst p)) , (⟶-prepend-⊤⊤ from to (snd p)) where
      p = ∧-⋙-lem c' c'' a b c'∥c'' a∥b a∧b⋙?c a⋙?c' b⋙c''
    ∧-⋙-lem (⊥∷ c') (⊥∷ c'') (⟨ from ⇒ to ⟩∷ a) (⊥∷ b) (⊥∥⊥ c'∥c'') (⊤∥⊥ a∥b) (⊤⋙?⊥ .from .to a∧b⋙?c) (⊤⋙?⊥ .from .to a⋙?c') (⊥⋙?⊥ b⋙c'') =
      (⟶-prepend-⊤⊤ from to (fst p)) , (⟶-prepend-⊤⊤ from to (snd p)) where
      p = ∧-⋙-lem c' c'' a b c'∥c'' a∥b a∧b⋙?c a⋙?c' b⋙c''
    ∧-⋙-lem (⊥∷ c') (⟨ from ⇒ to ⟩∷ c'') (⊥∷ a) (⟨ from₁ ⇒ .from ⟩∷ b) (⊥∥⊤ c'∥c'') (⊥∥⊤ a∥b) (⊤⋙?⊤ .from₁ .from .to a∧b⋙?c) (⊥⋙?⊥ a⋙?c') (⊤⋙?⊤ .from₁ .from .to b⋙c'') =
      (⟶-prepend-⊤⊤ from to (fst p)) , (⟶-prepend-⊤⊤ from to (snd p)) where
      p = ∧-⋙-lem c' c'' a b c'∥c'' a∥b a∧b⋙?c a⋙?c' b⋙c''
    ∧-⋙-lem (⟨ from ⇒ to ⟩∷ c') (⊥∷ c'') (⟨ from₁ ⇒ .from ⟩∷ a) (⊥∷ b) (⊤∥⊥ c'∥c'') (⊤∥⊥ a∥b) (⊤⋙?⊤ .from₁ .from .to a∧b⋙?c) (⊤⋙?⊤ .from₁ .from .to a⋙?c') (⊥⋙?⊥ b⋙c'') =
      (⟶-prepend-⊤⊤ from to (fst p)) , (⟶-prepend-⊤⊤ from to (snd p)) where
      p = ∧-⋙-lem c' c'' a b c'∥c'' a∥b a∧b⋙?c a⋙?c' b⋙c''

  -- ===============================
    ⋙-assoc : ∀ {n}{f₁ f₂ f₃ : Form n}{p₁ : Patch f₁}{p₂ : Patch f₂}{p₃ : Patch f₃}
      → (p₁⋙?p₂ : p₁ ⋙? p₂)
      → ([p₁⋙ₚp₂]⋙?p₃ : (p₁ ⋙ₚ p₂) p₁⋙?p₂ ⋙? p₃)
      → (p₂⋙?p₃ : p₂ ⋙? p₃)
      → (p₁⋙?[p₂⋙ₚp₃] : p₁ ⋙? (p₂ ⋙ₚ p₃) p₂⋙?p₃)
      → (((p₁ ⋙ₚ p₂) p₁⋙?p₂) ⋙ₚ p₃) [p₁⋙ₚp₂]⋙?p₃
        ⟷₂
        (p₁ ⋙ₚ (p₂ ⋙ₚ p₃) p₂⋙?p₃) p₁⋙?[p₂⋙ₚp₃]
    ⋙-assoc O⋙?O O⋙?O O⋙?O O⋙?O = (λ x x₁ → x₁ , refl) , (λ x x₁ → x₁ , refl)
    ⋙-assoc (⊥⋙?⊥ p₁⋙?p₂) (⊥⋙?⊥ [p₁⋙ₚp₂]⋙?p₃) (⊥⋙?⊥ p₂⋙?p₃) (⊥⋙?⊥ p₁⋙?[p₂⋙?p₃]) = 
      (⟶-prepend-⊥⊥ (fst p)) , (⟶-prepend-⊥⊥ (snd p)) where
      p = ⋙-assoc p₁⋙?p₂ [p₁⋙ₚp₂]⋙?p₃ p₂⋙?p₃ p₁⋙?[p₂⋙?p₃]
    ⋙-assoc (⊤⋙?⊥ from to p₁⋙?p₂) (⊤⋙?⊥ .from .to [p₁⋙ₚp₂]⋙?p₃) (⊥⋙?⊥ p₂⋙?p₃) (⊤⋙?⊥ .from .to p₁⋙?[p₂⋙?p₃]) = 
      (⟶-prepend-⊤⊤ from to (fst p)) , (⟶-prepend-⊤⊤ from to (snd p)) where
      p = ⋙-assoc p₁⋙?p₂ [p₁⋙ₚp₂]⋙?p₃ p₂⋙?p₃ p₁⋙?[p₂⋙?p₃]
    ⋙-assoc (⊤⋙?⊥ from to p₁⋙?p₂) (⊤⋙?⊤ .from .to to₂ [p₁⋙ₚp₂]⋙?p₃) () p₁⋙?[p₂⋙?p₃]
    ⋙-assoc (⊤⋙?⊤ from to to₂ p₁⋙?p₂) (⊤⋙?⊥ .to .to₂ [p₁⋙ₚp₂]⋙?p₃) (⊤⋙?⊥ .to .to₂ p₂⋙?p₃) (⊤⋙?⊤ .from .to .to₂ p₁⋙?[p₂⋙?p₃]) = 
      (⟶-prepend-⊤⊤ to to₂ (fst p)) , (⟶-prepend-⊤⊤ to to₂ (snd p)) where
      p = ⋙-assoc p₁⋙?p₂ [p₁⋙ₚp₂]⋙?p₃ p₂⋙?p₃ p₁⋙?[p₂⋙?p₃]
    ⋙-assoc (⊤⋙?⊤ from .to₂ to₂ p₁⋙?p₂) (⊤⋙?⊤ .to₂ .to₂ to₃ [p₁⋙ₚp₂]⋙?p₃) (⊤⋙?⊤ .to₂ .to₂ .to₃ p₂⋙?p₃) (⊤⋙?⊤ .from .to₂ .to₃ p₁⋙?[p₂⋙?p₃]) =
      (⟶-prepend-⊤⊤ to₂ to₃ (fst p)) , (⟶-prepend-⊤⊤ to₂ to₃ (snd p)) where
      p = ⋙-assoc p₁⋙?p₂ [p₁⋙ₚp₂]⋙?p₃ p₂⋙?p₃ p₁⋙?[p₂⋙?p₃]

  {- !!!!!!!
     Всё отсюда и до конца не нужно! 
     Оно для плохого определения ⟷
  -}
    
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
    -}
    

  -- c = c' ∧ c'' ⇒ (a ∧ b) ⋙ c ⟷ (a ⋙ c') ∧ (b ⋙ c'')
  -- Хорошая формулировка для плохого ⟷. Можно не читать
  ∧-⋙-lem : ∀ {n} {fᵃ fᵇ fᶜ' fᶜ'' : Form n}
    (c' : Patch fᶜ')(c'' : Patch fᶜ'')
    (a : Patch fᵃ)(b : Patch fᵇ)
    (c'∥c'' : fᶜ' ∥ fᶜ'') 
    (a∥b : fᵃ ∥ fᵇ)
    (a∧b⋙?c : (a ∧ₚ b) a∥b ⋙? ((c' ∧ₚ c'') c'∥c''))
    (a⋙?c' : a ⋙? c')
    (b⋙?c'' : b ⋙? c'')
    → (((a ∧ₚ b) a∥b) ⋙ₚ ((c' ∧ₚ c'') c'∥c'')) a∧b⋙?c 
      ⟷ ((a ⋙ₚ c') a⋙?c' ∧ₚ (b ⋙ₚ c'') b⋙?c'') a∥b
  ∧-⋙-lem O O O O []∥[] []∥[] O⋙?O O⋙?O O⋙?O [] []⊏[] []⊏[] = refl
  ∧-⋙-lem (⊥∷ c') (⊥∷ c'') (⊥∷ a) (⊥∷ b) (⊥∥⊥ c'∥c'') (⊥∥⊥ a∥b) (⊥⋙?⊥ a∧b⋙?c) (⊥⋙?⊥ a⋙?c') (⊥⋙?⊥ b⋙?c'') (x ∷ x₁) (⊥⊏ .x p₁⊏x) (⊥⊏ .x p₂⊏x) 
    = vec-prepend x (∧-⋙-lem c' c'' a b c'∥c'' a∥b a∧b⋙?c a⋙?c' b⋙?c'' x₁ p₁⊏x p₂⊏x)
  ∧-⋙-lem (⊥∷ c') (⊥∷ c'') (⊥∷ a) (⟨ .x ⇒ to ⟩∷ b) (⊥∥⊥ c'∥c'') (⊥∥⊤ a∥b) (⊤⋙?⊥ .x .to a∧b⋙?c) (⊥⋙?⊥ a⋙?c') (⊤⋙?⊥ .x .to b⋙?c'') (x ∷ x₁) (⊤⊏ .x .to p₁⊏x) (⊤⊏ .x .to p₂⊏x) 
    = vec-prepend to (∧-⋙-lem c' c'' a b c'∥c'' a∥b a∧b⋙?c a⋙?c' b⋙?c'' x₁ p₁⊏x p₂⊏x)
  ∧-⋙-lem (⊥∷ c') (⊥∷ c'') (⟨ .x ⇒ to ⟩∷ a) (⊥∷ b) (⊥∥⊥ c'∥c'') (⊤∥⊥ a∥b) (⊤⋙?⊥ .x .to a∧b⋙?c) (⊤⋙?⊥ .x .to a⋙?c') (⊥⋙?⊥ b⋙?c'') (x ∷ x₁) (⊤⊏ .x .to p₁⊏x) (⊤⊏ .x .to p₂⊏x) 
    = vec-prepend to (∧-⋙-lem c' c'' a b c'∥c'' a∥b a∧b⋙?c a⋙?c' b⋙?c'' x₁ p₁⊏x p₂⊏x)
  ∧-⋙-lem (⊥∷ c') (⟨ .x ⇒ to ⟩∷ c'') (⊥∷ a) (⟨ from ⇒ .x ⟩∷ b) (⊥∥⊤ c'∥c'') (⊥∥⊤ a∥b) (⊤⋙?⊤ .from .x .to a∧b⋙?c) (⊥⋙?⊥ a⋙?c') (⊤⋙?⊤ .from .x .to b⋙?c'') (x ∷ x₁) (⊤⊏ .x .to p₁⊏x) (⊤⊏ .x .to p₂⊏x) 
    = vec-prepend to (∧-⋙-lem c' c'' a b c'∥c'' a∥b a∧b⋙?c a⋙?c' b⋙?c'' x₁ p₁⊏x p₂⊏x)
  ∧-⋙-lem (⟨ .x ⇒ to ⟩∷ c') (⊥∷ c'') (⟨ from ⇒ .x ⟩∷ a) (⊥∷ b) (⊤∥⊥ c'∥c'') (⊤∥⊥ a∥b) (⊤⋙?⊤ .from .x .to a∧b⋙?c) (⊤⋙?⊤ .from .x .to a⋙?c') (⊥⋙?⊥ b⋙?c'') (x ∷ x₁) (⊤⊏ .x .to p₁⊏x) (⊤⊏ .x .to p₂⊏x) 
    = vec-prepend to (∧-⋙-lem c' c'' a b c'∥c'' a∥b a∧b⋙?c a⋙?c' b⋙?c'' x₁ p₁⊏x p₂⊏x)


  -- (p₁ ⋙ p₂) ⋙ p₃ ⟷ p₁ ⋙ (p₂ ⋙ p₃)
  ⋙-assoc : ∀ {n}{f₁ f₂ f₃ : Form n}{p₁ : Patch f₁}{p₂ : Patch f₂}{p₃ : Patch f₃}
    → (p₁⋙?p₂ : p₁ ⋙? p₂)
    → ([p₁⋙ₚp₂]⋙?p₃ : (p₁ ⋙ₚ p₂) p₁⋙?p₂ ⋙? p₃)
    → (p₂⋙?p₃ : p₂ ⋙? p₃)
    → (p₁⋙?[p₂⋙ₚp₃] : p₁ ⋙? (p₂ ⋙ₚ p₃) p₂⋙?p₃)
    → (((p₁ ⋙ₚ p₂) p₁⋙?p₂) ⋙ₚ p₃) [p₁⋙ₚp₂]⋙?p₃
      ⟷
      (p₁ ⋙ₚ (p₂ ⋙ₚ p₃) p₂⋙?p₃) p₁⋙?[p₂⋙ₚp₃]
  ⋙-assoc O⋙?O O⋙?O O⋙?O O⋙?O [] []⊏[] []⊏[] = refl
  ⋙-assoc (⊥⋙?⊥ p₁⋙?p₂) (⊥⋙?⊥ [p₁⋙?p₂]⋙?p₃) (⊥⋙?⊥ p₂⋙?p₃) (⊥⋙?⊥ p₁⋙?[p₂⋙ₚp₃]) (x ∷ x₁) (⊥⊏ .x p₁⊏x) (⊥⊏ .x p₂⊏x) = 
    vec-prepend x (⋙-assoc p₁⋙?p₂ [p₁⋙?p₂]⋙?p₃ p₂⋙?p₃ p₁⋙?[p₂⋙ₚp₃] x₁ p₁⊏x p₂⊏x)
  ⋙-assoc (⊤⋙?⊥ .x to p₁⋙?p₂) (⊤⋙?⊥ .x .to [p₁⋙?p₂]⋙?p₃) (⊥⋙?⊥ p₂⋙?p₃) (⊤⋙?⊥ .x .to p₁⋙?[p₂⋙ₚp₃]) (x ∷ x₁) (⊤⊏ .x .to p₁⊏x) (⊤⊏ .x .to p₂⊏x) = 
    vec-prepend to (⋙-assoc p₁⋙?p₂ [p₁⋙?p₂]⋙?p₃ p₂⋙?p₃ p₁⋙?[p₂⋙ₚp₃] x₁ p₁⊏x p₂⊏x)
  ⋙-assoc (⊤⋙?⊤ from .x to₂ p₁⋙?p₂) (⊤⋙?⊥ .x .to₂ [p₁⋙?p₂]⋙?p₃) (⊤⋙?⊥ .x .to₂ p₂⋙?p₃) (⊤⋙?⊤ .from .x .to₂ p₁⋙?[p₂⋙ₚp₃]) (x ∷ x₁) (⊤⊏ .x .to₂ p₁⊏x) (⊤⊏ .x .to₂ p₂⊏x) = 
    vec-prepend to₂ (⋙-assoc p₁⋙?p₂ [p₁⋙?p₂]⋙?p₃ p₂⋙?p₃ p₁⋙?[p₂⋙ₚp₃] x₁ p₁⊏x p₂⊏x)
  ⋙-assoc (⊤⋙?⊤ from .x .x p₁⋙?p₂) (⊤⋙?⊤ .x .x to₂ [p₁⋙?p₂]⋙?p₃) (⊤⋙?⊤ .x .x .to₂ p₂⋙?p₃) (⊤⋙?⊤ .from .x .to₂ p₁⋙?[p₂⋙ₚp₃]) (x ∷ x₁) (⊤⊏ .x .to₂ p₁⊏x) (⊤⊏ .x .to₂ p₂⊏x) = 
    vec-prepend to₂ (⋙-assoc p₁⋙?p₂ [p₁⋙?p₂]⋙?p₃ p₂⋙?p₃ p₁⋙?[p₂⋙ₚp₃] x₁ p₁⊏x p₂⊏x)
