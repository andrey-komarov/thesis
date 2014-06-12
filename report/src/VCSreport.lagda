\begin{code}
module VCSreport where

open import OXIj.BrutalDepTypes

module With-⋀-and-⋙ (A : Set) (eqA : (a b : A) → Dec (a ≡ b)) where

  open Data-Vec
  open ≡-Prop

  Form : ℕ → Set
  Form = Vec Bool 

  data _∥_ : ∀ {n} → Form n → Form n → Set where
    []∥[] : [] ∥ []
    ⊥∥⊥ : ∀ {n}{f₁ f₂ : Form n} → f₁ ∥ f₂ → (false ∷ f₁) ∥ (false ∷ f₂)
    ⊤∥⊥ : ∀ {n}{f₁ f₂ : Form n} → f₁ ∥ f₂ → (true ∷ f₁) ∥ (false ∷ f₂)
    ⊥∥⊤ : ∀ {n}{f₁ f₂ : Form n} → f₁ ∥ f₂ → (false ∷ f₁) ∥ (true ∷ f₂)

  data Patch : ∀ {n} → Form n → Set where
    O : Patch []
    ⊥∷ : ∀ {n}{f : Form n} → Patch f → Patch (false ∷ f)
    ⟨_⇒_⟩∷_ : ∀ {n}{f : Form n}
      → (from to : A)
      → Patch f → Patch (true ∷ f)

  data _⊂_ : ∀ {n} → Form n → Form n → Set where
    []⊂[] : [] ⊂ []
    ⊂⊤ : ∀ {n}{f₁ f₂ : Form n} → (b : Bool) → (b ∷ f₁) ⊂ (true ∷ f₂)
    ⊥⊂⊥ : ∀ {n}{f₁ f₂ : Form n} → (false ∷ f₁) ⊂ (false ∷ f₂)

  data _⊏_ : ∀ {n}{f : Form n} → Patch f → Vec A n → Set where
    []⊏[] : O ⊏ []
    ⊥⊏ : ∀ {n}{f : Form n}{p : Patch f}{v : Vec A n}
      → (a : A) → p ⊏ v → (⊥∷ p) ⊏ (a ∷ v)
    ⊤⊏ : ∀ {n}{f : Form n}{p : Patch f}{v : Vec A n}
      → (a b : A)
      → p ⊏ v → (⟨ a ⇒ b ⟩∷ p) ⊏ (a ∷ v)

  patch : ∀ {n}{f : Form n} → (p : Patch f) → (x : Vec A n) → p ⊏ x → Vec A n
  patch O [] []⊏[] = []
  patch (⊥∷ p) (x ∷ xs) (⊥⊏ .x p-xs) = x ∷ patch p xs p-xs
  patch (⟨ .f ⇒ t ⟩∷ p) (f ∷ xs) (⊤⊏ .f .t p-xs) = 
    t ∷ patch p xs p-xs

  _⟶_ : ∀ {n}{f₁ f₂ : Form n}
    → (p₁ : Patch f₁) → (p₂ : Patch f₂) → Set
  _⟶_ {n} p₁ p₂ = ∀ (x : Vec A n) 
    → (p₁-x : p₁ ⊏ x) → Σ (p₂ ⊏ x) (λ p₂-x → 
      (patch p₁ x p₁-x ≡ patch p₂ x p₂-x))

  _⟷_ : ∀ {n}{f₁ f₂ : Form n}
    → (p₁ : Patch f₁) → (p₂ : Patch f₂) → Set
  p₁ ⟷ p₂ = (p₁ ⟶ p₂) ∧ (p₂ ⟶ p₁)

  module ⟷-equiv where
    ⟷-refl : ∀ {n}{f : Form n} → (p : Patch f)
      → p ⟷ p
    ⟷-refl p = (λ x x₁ → x₁ , refl) , (λ x x₁ → x₁ , refl)

    ⟶-trans : ∀ {n}{f₁ f₂ f₃ : Form n}
      → {p₁ : Patch f₁}{p₂ : Patch f₂}{p₃ : Patch f₃}
      → (p₁ ⟶ p₂) → (p₂ ⟶ p₃) → (p₁ ⟶ p₃)
    ⟶-trans {p₁ = p₁}{p₂}{p₃} p₁⟶p₂ p₂⟶p₃ x p₁⊏x 
      with patch p₁ x p₁⊏x | p₁⟶p₂ x p₁⊏x
    ... | .(patch p₂ x p₂⊏x) | p₂⊏x , refl = p₂⟶p₃ x p₂⊏x
  
    ⟷-trans : ∀ {n}{f₁ f₂ f₃ : Form n}
      → {p₁ : Patch f₁}{p₂ : Patch f₂}{p₃ : Patch f₃}
      → (p₁ ⟷ p₂) → (p₂ ⟷ p₃) → (p₁ ⟷ p₃)
    ⟷-trans (p₁⟶p₂ , p₂⟶p₁) (p₂⟶p₃ , p₃⟶p₂) = 
      (⟶-trans p₁⟶p₂ p₂⟶p₃) , (⟶-trans p₃⟶p₂ p₂⟶p₁)
      
    ⟷-symm : ∀ {n}{f₁ f₂ : Form n}
      → {p₁ : Patch f₁} {p₂ : Patch f₂}
      → (p₁ ⟷ p₂) → (p₂ ⟷ p₁)
    ⟷-symm p₁⟷p₂ = snd p₁⟷p₂ , fst p₁⟷p₂

  open ⟷-equiv

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

  module ⟷-∧-lemmas where

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
      → ((p₁ ∧ₚ p₂) f₁∥f₂) ⟷ ((p₂ ∧ₚ p₁) (∥-comm f₁∥f₂))
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
        ⟷ 
        (p₁ ∧ₚ (p₂ ∧ₚ p₃) f₂∥f₃) 
          (∥-comm (lemma-∥-unite f₂∥f₃ (∥-comm f₁∥f₃) (∥-comm f₁∥f₂)))

    ∧-trans []∥[] []∥[] []∥[] O O O = 
      (λ x x₁ → x₁ , refl) , (λ x x₁ → x₁ , refl)
    ∧-trans (⊥∥⊥ f₁∥f₂) (⊥∥⊥ f₂∥f₃) (⊥∥⊥ f₁∥f₃) (⊥∷ p₁) (⊥∷ p₂) (⊥∷ p₃) = 
      (⟶-prepend-⊥⊥ (fst p)) , (⟶-prepend-⊥⊥ (snd p)) where
      p = ∧-trans f₁∥f₂ f₂∥f₃ f₁∥f₃ p₁ p₂ p₃
    ∧-trans (⊥∥⊥ f₁∥f₂) (⊥∥⊤ f₂∥f₃) (⊥∥⊤ f₁∥f₃) (⊥∷ p₁) (⊥∷ p₂) 
      (⟨ from ⇒ to ⟩∷ p₃) = 
      (⟶-prepend-⊤⊤ from to (fst p)) , (⟶-prepend-⊤⊤ from to (snd p)) where
      p = ∧-trans f₁∥f₂ f₂∥f₃ f₁∥f₃ p₁ p₂ p₃
    ∧-trans (⊤∥⊥ f₁∥f₂) (⊥∥⊥ f₂∥f₃) (⊤∥⊥ f₁∥f₃) 
      (⟨ from ⇒ to ⟩∷ p₁) (⊥∷ p₂) (⊥∷ p₃) = 
      (⟶-prepend-⊤⊤ from to (fst p)) , (⟶-prepend-⊤⊤ from to (snd p)) where 
      p = ∧-trans f₁∥f₂ f₂∥f₃ f₁∥f₃ p₁ p₂ p₃
    ∧-trans (⊤∥⊥ f₁∥f₂) (⊥∥⊤ f₂∥f₃) () p₁ p₂ p₃
    ∧-trans (⊥∥⊤ f₁∥f₂) (⊤∥⊥ f₂∥f₃) (⊥∥⊥ f₁∥f₃) (⊥∷ p₁) 
      (⟨ from ⇒ to ⟩∷ p₂) (⊥∷ p₃) = 
      (⟶-prepend-⊤⊤ from to (fst p)) , (⟶-prepend-⊤⊤ from to (snd p)) where 
      p = ∧-trans f₁∥f₂ f₂∥f₃ f₁∥f₃ p₁ p₂ p₃

  data _⋙?_ : ∀ {n}{f₁ f₂ : Form n} → Patch f₁ → Patch f₂ → Set where  
    O⋙?O : O ⋙? O
    ⊥⋙?⊥ : ∀ {n}{f₁ f₂ : Form n} {p₁ : Patch f₁} {p₂ : Patch f₂}
      → (p₁ ⋙? p₂) → (⊥∷ p₁) ⋙? (⊥∷ p₂)
    ⊤⋙?⊥ : ∀ {n}{f₁ f₂ : Form n} {p₁ : Patch f₁} {p₂ : Patch f₂}
      → (from to : A) → (p₁ ⋙? p₂)
      → (⟨ from ⇒ to ⟩∷ p₁) ⋙? (⊥∷ p₂)
    ⊤⋙?⊤ : ∀ {n}{f₁ f₂ : Form n} {p₁ : Patch f₁} {p₂ : Patch f₂}
      → (from to to₂ : A) → (p₁ ⋙? p₂)
      → (⟨ from ⇒ to ⟩∷ p₁) ⋙? (⟨ to ⇒ to₂ ⟩∷ p₂)

  _⋙ₚ_ : ∀ {n} {f₁ f₂ : Form n} (p₁ : Patch f₁) (p₂ : Patch f₂)
    → (p₁ ⋙? p₂) → Patch f₁
  _⋙ₚ_ O O O⋙?O = O
  _⋙ₚ_ (⊥∷ p₁) (⊥∷ p₂) (⊥⋙?⊥ p₁-p₂) = ⊥∷ ((p₁ ⋙ₚ p₂) p₁-p₂)
  _⋙ₚ_ (⟨ a ⇒ b ⟩∷ p₁) (⊥∷ p₂) (⊤⋙?⊥ .a .b p₁-p₂) = 
    ⟨ a ⇒ b ⟩∷ ((p₁ ⋙ₚ p₂) p₁-p₂)
  _⋙ₚ_ (⟨ a ⇒ .b ⟩∷ p₁) (⟨ b ⇒ c ⟩∷ p₂) (⊤⋙?⊤ .a .b .c p₁-p₂) = 
    ⟨ a ⇒ c ⟩∷ ((p₁ ⋙ₚ p₂) p₁-p₂)

  module ⟷-⋙-lemmas where

    ∧-⋙-lem : ∀ {n} {fᵃ fᵇ fᶜ' fᶜ'' : Form n}
      (c' : Patch fᶜ')(c'' : Patch fᶜ'')
      (a : Patch fᵃ)(b : Patch fᵇ)
      (c'∥c'' : fᶜ' ∥ fᶜ'') 
      (a∥b : fᵃ ∥ fᵇ)
      (a∧b>>>?c : (a ∧ₚ b) a∥b ⋙? ((c' ∧ₚ c'') c'∥c''))
      (a>>>?c' : a ⋙? c')
      (b>>>?c'' : b ⋙? c'')
      → (((a ∧ₚ b) a∥b) ⋙ₚ ((c' ∧ₚ c'') c'∥c'')) a∧b>>>?c 
        ⟷ ((a ⋙ₚ c') a>>>?c' ∧ₚ (b ⋙ₚ c'') b>>>?c'') a∥b

    ∧-⋙-lem O O O O []∥[] []∥[] O⋙?O O⋙?O O⋙?O = 
      (λ x x₁ → x₁ , refl) , (λ x x₁ → x₁ , refl)
    ∧-⋙-lem (⊥∷ c') (⊥∷ c'') (⊥∷ a) (⊥∷ b) (⊥∥⊥ c'∥c'') (⊥∥⊥ a∥b) 
      (⊥⋙?⊥ a∧b⋙?c) (⊥⋙?⊥ a⋙?c') (⊥⋙?⊥ b⋙c'') = 
      (⟶-prepend-⊥⊥ (fst p)) , (⟶-prepend-⊥⊥ (snd p)) where
      p = ∧-⋙-lem c' c'' a b c'∥c'' a∥b a∧b⋙?c a⋙?c' b⋙c''
    ∧-⋙-lem (⊥∷ c') (⊥∷ c'') (⊥∷ a) (⟨ from ⇒ to ⟩∷ b) (⊥∥⊥ c'∥c'') (⊥∥⊤ a∥b) 
      (⊤⋙?⊥ .from .to a∧b⋙?c) (⊥⋙?⊥ a⋙?c') (⊤⋙?⊥ .from .to b⋙c'') = 
      (⟶-prepend-⊤⊤ from to (fst p)) , (⟶-prepend-⊤⊤ from to (snd p)) where
      p = ∧-⋙-lem c' c'' a b c'∥c'' a∥b a∧b⋙?c a⋙?c' b⋙c''
    ∧-⋙-lem (⊥∷ c') (⊥∷ c'') (⟨ from ⇒ to ⟩∷ a) (⊥∷ b) (⊥∥⊥ c'∥c'') (⊤∥⊥ a∥b) 
      (⊤⋙?⊥ .from .to a∧b⋙?c) (⊤⋙?⊥ .from .to a⋙?c') (⊥⋙?⊥ b⋙c'') =
      (⟶-prepend-⊤⊤ from to (fst p)) , (⟶-prepend-⊤⊤ from to (snd p)) where
      p = ∧-⋙-lem c' c'' a b c'∥c'' a∥b a∧b⋙?c a⋙?c' b⋙c''
    ∧-⋙-lem (⊥∷ c') (⟨ from ⇒ to ⟩∷ c'') (⊥∷ a) (⟨ from₁ ⇒ .from ⟩∷ b) 
      (⊥∥⊤ c'∥c'') (⊥∥⊤ a∥b) (⊤⋙?⊤ .from₁ .from .to a∧b⋙?c) (⊥⋙?⊥ a⋙?c') 
      (⊤⋙?⊤ .from₁ .from .to b⋙c'') = 
      (⟶-prepend-⊤⊤ from₁ to (fst p)) , ⟶-prepend-⊤⊤ from₁ to (snd p) where
      p = ∧-⋙-lem c' c'' a b c'∥c'' a∥b a∧b⋙?c a⋙?c' b⋙c''
    ∧-⋙-lem (⟨ from ⇒ to ⟩∷ c') (⊥∷ c'') (⟨ from₁ ⇒ .from ⟩∷ a) (⊥∷ b) 
      (⊤∥⊥ c'∥c'') (⊤∥⊥ a∥b) (⊤⋙?⊤ .from₁ .from .to a∧b⋙?c) 
      (⊤⋙?⊤ .from₁ .from .to a⋙?c') (⊥⋙?⊥ b⋙c'') =
      (⟶-prepend-⊤⊤ from₁ to (fst p)) , ⟶-prepend-⊤⊤ from₁ to (snd p) where
      p = ∧-⋙-lem c' c'' a b c'∥c'' a∥b a∧b⋙?c a⋙?c' b⋙c''

    ⋙-assoc : ∀ {n}{f₁ f₂ f₃ : Form n}{p₁ : Patch f₁}{p₂ : Patch f₂}{p₃ : Patch f₃}
      → (p₁>>?p₂ : p₁ ⋙? p₂)
      → ([p₁>>ₚp₂]>>?p₃ : (p₁ ⋙ₚ p₂) p₁>>?p₂ ⋙? p₃)
      → (p₂>>?p₃ : p₂ ⋙? p₃)
      → (p₁>>?[p₂>>ₚp₃] : p₁ ⋙? (p₂ ⋙ₚ p₃) p₂>>?p₃)
      → (((p₁ ⋙ₚ p₂) p₁>>?p₂) ⋙ₚ p₃) [p₁>>ₚp₂]>>?p₃
        ⟷
        (p₁ ⋙ₚ (p₂ ⋙ₚ p₃) p₂>>?p₃) p₁>>?[p₂>>ₚp₃]
    ⋙-assoc O⋙?O O⋙?O O⋙?O O⋙?O = (λ x x₁ → x₁ , refl) , (λ x x₁ → x₁ , refl)
    ⋙-assoc (⊥⋙?⊥ p₁⋙?p₂) (⊥⋙?⊥ [p₁⋙p₂]⋙?p₃) (⊥⋙?⊥ p₂⋙?p₃) (⊥⋙?⊥ p₁⋙?[p₂⋙p₃]) = 
      (⟶-prepend-⊥⊥ (fst p)) , (⟶-prepend-⊥⊥ (snd p)) where
      p = ⋙-assoc p₁⋙?p₂ [p₁⋙p₂]⋙?p₃ p₂⋙?p₃ p₁⋙?[p₂⋙p₃]
    ⋙-assoc (⊤⋙?⊥ from to p₁⋙?p₂) (⊤⋙?⊥ .from .to [p₁⋙p₂]⋙?p₃) 
      (⊥⋙?⊥ p₂⋙?p₃) (⊤⋙?⊥ .from .to p₁⋙?[p₂⋙p₃]) = 
      (⟶-prepend-⊤⊤ from to (fst p)) , ⟶-prepend-⊤⊤ from to (snd p) where
      p = ⋙-assoc p₁⋙?p₂ [p₁⋙p₂]⋙?p₃ p₂⋙?p₃ p₁⋙?[p₂⋙p₃]
    ⋙-assoc (⊤⋙?⊤ from to to₂ p₁⋙?p₂) (⊤⋙?⊥ .from .to₂ [p₁⋙p₂]⋙?p₃) 
      (⊤⋙?⊥ .to .to₂ p₂⋙?p₃) (⊤⋙?⊤ .from .to .to₂ p₁⋙?[p₂⋙p₃]) = 
      (⟶-prepend-⊤⊤ from to₂ (fst p)) , ⟶-prepend-⊤⊤ from to₂ (snd p) where
      p = ⋙-assoc p₁⋙?p₂ [p₁⋙p₂]⋙?p₃ p₂⋙?p₃ p₁⋙?[p₂⋙p₃]
    ⋙-assoc (⊤⋙?⊤ from to to₂ p₁⋙?p₂) (⊤⋙?⊤ .from .to₂ to₃ [p₁⋙p₂]⋙?p₃) 
      (⊤⋙?⊤ .to .to₂ .to₃ p₂⋙?p₃) (⊤⋙?⊤ .from .to .to₃ p₁⋙?[p₂⋙p₃]) = 
      (⟶-prepend-⊤⊤ from to₃ (fst p)) , ⟶-prepend-⊤⊤ from to₃ (snd p) where
      p = ⋙-assoc p₁⋙?p₂ [p₁⋙p₂]⋙?p₃ p₂⋙?p₃ p₁⋙?[p₂⋙p₃]

  drop : ∀ {n} (b₁ b₂ : Bool) (f₁ f₂ : Form n)
    → (b₁ ∷ f₁) ∥ (b₂ ∷ f₂) → f₁ ∥ f₂
  drop .false .false f₃ f₄ (⊥∥⊥ p) = p
  drop .true .false f₃ f₄ (⊤∥⊥ p) = p
  drop .false .true f₃ f₄ (⊥∥⊤ p) = p

  ∥-dec : ∀ {n} (f₁ f₂ : Form n) → Dec (f₁ ∥ f₂)
  ∥-dec [] [] = yes []∥[]
  ∥-dec (true ∷ f₁) (true ∷ f₂) = no (no-tt f₁ f₂) where
    no-tt : ∀ {n} (f₁ f₂ : Form n) → ¬ ((true ∷ f₁) ∥ (true ∷ f₂))
    no-tt _ _ ()
  ∥-dec (true ∷ f₁) (false ∷ f₂) with ∥-dec f₁ f₂
  ... | yes a = yes (⊤∥⊥ a)
  ... | no ¬a = no (¬a ∘ drop true false f₁ f₂) where
  ∥-dec (false ∷ f₁) (true ∷ f₂) with ∥-dec f₁ f₂
  ... | yes a = yes (⊥∥⊤ a)
  ... | no ¬a = no (¬a ∘ drop false true f₁ f₂)
  ∥-dec (false ∷ f₁) (false ∷ f₂) with ∥-dec f₁ f₂
  ... | yes a = yes (⊥∥⊥ a)
  ... | no ¬a = no (¬a ∘ drop false false f₁ f₂)
  
  ⋙?-dec : ∀ {n} {f₁ f₂ : Form n} (p₁ : Patch f₁) (p₂ : Patch f₂)
    → Dec (p₁ ⋙? p₂)
  ⋙?-dec O O = yes O⋙?O
  ⋙?-dec (⊥∷ p₁) (⊥∷ p₂) with ⋙?-dec p₁ p₂ 
  ... | yes a = yes (⊥⋙?⊥ a)
  ... | no ¬a = no (¬a ∘ ⊥⊥-drop) where
    ⊥⊥-drop : ⊥∷ p₁ ⋙? ⊥∷ p₂ → p₁ ⋙? p₂
    ⊥⊥-drop (⊥⋙?⊥ p) = p
  ⋙?-dec (⊥∷ p₁) (⟨ from ⇒ to ⟩∷ p₂) = no fail where
    fail : ⊥∷ p₁ ⋙? (⟨ from ⇒ to ⟩∷ p₂) → ⊥
    fail ()
  ⋙?-dec (⟨ from ⇒ to ⟩∷ p₁) (⊥∷ p₂) with ⋙?-dec p₁ p₂
  ... | yes a = yes (⊤⋙?⊥ from to a)
  ... | no ¬a = no (¬a ∘ ⊤⊥-drop) where
    ⊤⊥-drop : ∀ {a b : A} → (⟨ a ⇒ b ⟩∷ p₁) ⋙? ⊥∷ p₂ → p₁ ⋙? p₂
    ⊤⊥-drop (⊤⋙?⊥ _ _ p) = p
  ⋙?-dec (⟨ from₁ ⇒ to₁ ⟩∷ p₁) (⟨ from₂ ⇒ to₂ ⟩∷ p₂) with ⋙?-dec p₁ p₂
  ... | yes a = cmp (eqA to₁ from₂) where
    cmp : Dec (to₁ ≡ from₂) 
      → Dec ((⟨ from₁ ⇒ to₁ ⟩∷ p₁) ⋙? (⟨ from₂ ⇒ to₂ ⟩∷ p₂))
    cmp (yes aa) rewrite aa = yes (⊤⋙?⊤ from₁ from₂ to₂ a)
    cmp (no ¬a) = no (¬a ∘ ends-eq) where
      ends-eq : ∀ {a b c d : A} → (⟨ a ⇒ b ⟩∷ p₁) ⋙? (⟨ c ⇒ d ⟩∷ p₂) → b ≡ c
      ends-eq (⊤⋙?⊤ a c d p) = refl
  ... | no ¬a = no (¬a ∘ ⊤⊤-drop) where
    ⊤⊤-drop : ∀ {a b c d} → (⟨ a ⇒ b ⟩∷ p₁) ⋙? (⟨ c ⇒ d ⟩∷ p₂) → p₁ ⋙? p₂
    ⊤⊤-drop (⊤⋙?⊤ _ _ _ p) = p

\end{code}
