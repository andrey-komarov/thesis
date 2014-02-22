module VCS where

open import OXIj.BrutalDepTypes

module TreeLikePatch (a : Set) where

  data Tree : Set where
    Nil : Tree
    Node : a → Tree → Tree → Tree
  
  data PTree : Set where
    Nil : PTree -- ниже неважно, что
    Expect : Tree → PTree -- ниже ровно это
    Node : PTree → PTree → PTree
    
  data PatchTree : PTree → Set where
    Nil : PatchTree Nil
    Match : (t₁ t₂ : Tree) → PatchTree (Expect t₁)
    Node : ∀ {t₁ t₂} 
      → (left : PatchTree t₁) → (right : PatchTree t₂)
      → PatchTree (Node t₁ t₂)
    
  data _⊳_ : ∀ {pt} 
    → (lhs : PatchTree pt) → (rhs : PatchTree pt) → Set where
    Id : ∀ {pt}{P : PatchTree pt} → P ⊳ P

  data _∩_ : ∀ {pt}
    → (PatchTree pt) → (PatchTree pt) → Set where
    Left : ∀ {ptₗ ptᵣ}{P₁ P₂ : PatchTree ptₗ}
      → P₁ ∩ P₂ → (P : PatchTree ptᵣ) → Node P₁ P ∩ Node P₂ P
    Right : ∀ {ptₗ ptᵣ}{P₁ P₂ : PatchTree ptᵣ}
      → (P : PatchTree ptₗ) → P₁ ∩ P₂ → Node P P₁ ∩ Node P P₂
      
  data Compatible : ∀ {pt} → PatchTree pt → PatchTree pt → Set where
    
module RepositoryFromTree (a : Set) where

  open TreeLikePatch a
  
  data Patch : PTree → PTree → Set where
    Init : ∀ {p} → (PatchTree p) → Patch p p
    _⋀_ : ∀ {t} → Patch t t → Patch t t → Patch t t
    _⋁_ : ∀ {t} → Patch t t → Patch t t → Patch t t
    _⋙_ : ∀ {t} → Patch t t → Patch t t → Patch t t

  data _⟷_ : ∀ {pt₁ pt₂} 
    → (L : Patch pt₁ pt₂) → (R : Patch pt₁ pt₂) → Set where
    -- ∨-idp : ∀ {pt₁ pt₂}{P : Patch pt₁ pt₂} → P ⟷ (P ∨ P)
    
    
module VecLikePatch (A : Set) where

  open Data-Vec

  data _⁇ (A : Set) : Set where
    ø : A ⁇
    ⊙ : (a : A) → A ⁇
    
  Req : ℕ → Set
  Req n = Vec (A ⁇) n
  
  Data : ℕ → Set
  Data n = Vec A n
    
  data _⊑_ : ∀ {n} → Req n → Data n → Set where
    empty : [] ⊑ []
    skip : ∀ {n}{a}{vₗ : Req n}{vᵣ : Data n}
      → (vₗ ⊑ vᵣ) → (ø ∷ vₗ) ⊑ (a ∷ vᵣ)
    get : ∀ {n}{a}{vₗ : Req n}{vᵣ : Data n}
      → (vₗ ⊑ vᵣ) → (⊙ a ∷ vₗ) ⊑ (a ∷ vᵣ)
    
  data Compatible : ∀ {n} → Req n → Req n → Set where
    empty : Compatible [] []
    ⊙-ø : ∀ {n}{a}{r₁ r₂ : Req n}
      → Compatible r₁ r₂ → Compatible (⊙ a ∷ r₁) (ø ∷ r₂)
    ø-⊙ : ∀ {n}{a}{r₁ r₂ : Req n}
      → Compatible r₁ r₂ → Compatible (ø ∷ r₁) (⊙ a ∷ r₂)
    ø-ø : ∀ {n}{r₁ r₂ : Req n}
      → Compatible r₁ r₂ → Compatible (ø ∷ r₁) (ø ∷ r₂)
      
  unite : ∀ {n} → (r₁ : Req n) → (r₂ : Req n) → (Compatible r₁ r₂) → Req n
  unite .[] .[] empty = []
  unite .(⊙ a ∷ r₁) .(ø ∷ r₂) (⊙-ø {n} {a} {r₁} {r₂} c) 
    = ⊙ a ∷ unite r₁ r₂ c
  unite .(ø ∷ r₁) .(⊙ a ∷ r₂) (ø-⊙ {n} {a} {r₁} {r₂} c) 
    = ⊙ a ∷ unite r₁ r₂ c
  unite .(ø ∷ r₁) .(ø ∷ r₂) (ø-ø {n} {r₁} {r₂} c) 
    = ø ∷ unite r₁ r₂ c
    
  _≫_ : ∀ {n} → (r₁ : Req n) → (r₂ : Req n) → Req n
  [] ≫ [] = []
  (ø ∷ r₁) ≫ (x₂ ∷ r₂) = x₂ ∷ (r₁ ≫ r₂)
  (⊙ a ∷ r₁) ≫ (ø ∷ r₂) = ⊙ a ∷ (r₁ ≫ r₂)
  (⊙ a₁ ∷ r₁) ≫ (⊙ a₂ ∷ r₂) = ⊙ a₂ ∷ (r₁ ≫ r₂)
  
module RepositoryFromVec (A : Set) where
  
  open Data-Vec
  open VecLikePatch A
  
  data _⟹_ : ∀ {n} → Req n → Req n → Set where
    Init : ∀ {n} (from : Req n) → (to : Req n) → from ⟹ to
    _⋀_ : ∀ {n}{f₁ t₁ f₂ t₂ : Req n} → (f₁ ⟹ t₁) → (f₂ ⟹ t₂)
      → (cf : Compatible f₁ f₂) → (ct : Compatible t₁ t₂)
      → (unite f₁ f₂ cf ⟹ unite t₁ t₂ ct)
    _⋙_ : ∀ {n}{f₁ t₁ f₂ t₂ : Req n} → (f₁ ⟹ t₁) → (f₂ ⟹ t₂)
      → (f₁ ≫ f₂) ⟹ (t₁ ≫ t₂)
      
  patch : ∀ {n}{f t : Req n} → (f ⟹ t) → Data n → Data n
  patch (Init f t) [] = []
  patch (Init (f ∷ xf) (ø ∷ xt)) (x ∷ xs) = x ∷ patch (Init xf xt) xs
  patch (Init (f ∷ xf) (⊙ a ∷ xt)) (x ∷ xs) = a ∷ patch (Init xf xt) xs
  patch ((f₁ ⋀ f₂) cf ct) x = (patch f₁ ∘ patch f₂) x
  patch (f₁ ⋙ f₂) x = (patch f₂ ∘ patch f₁) x
  
  _⟷_ : ∀ {n}{f₁ t₁ f₂ t₂ : Req n} → (f₁ ⟹ t₁) → (f₂ ⟹ t₂) → Set
  _⟷_ {n} p₁ p₂ = ∀ (x : Data n) → patch p₁ x ≡ patch p₂ x
  
  --⋀-is-⋙ : ∀ {n}{p₁ p₂ : Req n} → (c : Compatible p₁ p₂)
  --  → ((p₁ ⋀ p₂) c) ⟷ (p₁ ⋙ p₂)
  --⋀-is-⋙\gtr {n}{p₁}{p₂} c = ?

