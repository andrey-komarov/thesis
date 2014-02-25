module VCS where

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


module VecLikePatch2 (A : Set) where

  open Data-Vec
  open Data-Maybe

  Data : ℕ → Set
  Data n = Vec A n

  SimplePatch : ℕ → Set
  SimplePatch n = Vec ((A × A) ⁇) n

  Known : ℕ → Set
  Known n = Vec (A ⁇) n

  data _∥_ {A : Set} : ∀ {n} → Vec (A ⁇) n → Vec (A ⁇) n → Set where
    []∥[] : [] ∥ []
    ø-ø : ∀ {n} {p₁ p₂ : Vec (A ⁇) n} → p₁ ∥ p₂ → (ø ∷ p₁) ∥ (ø ∷ p₂)
    ø-⊙ : ∀ {n} {p₁ p₂ : Vec (A ⁇) n} → (a : A)
      → p₁ ∥ p₂ → (ø ∷ p₁) ∥ (⊙ a ∷ p₂)
    ⊙-ø : ∀ {n} {p₁ p₂ : Vec (A ⁇) n} → (a : A)
      → p₁ ∥ p₂ → (⊙ a ∷ p₁) ∥ (ø ∷ p₂)
      
  map : ∀ {n}{A B : Set} → (f : A → B) → Vec A n → Vec B n
  map f [] = []
  map f (x ∷ v) = f x ∷ map f v

  dom : ∀ {n} → SimplePatch n → Known n
  dom = map $ map⁇ projl
    
  codom : ∀ {n} → SimplePatch n → Known n
  codom = map $ map⁇ projr
      
  data CanApply : ∀ {n} → SimplePatch n → Data n → Set where

  simplePatch : ∀ {n} → (p : SimplePatch n) → (x : Data n) → Data n
  -- слишком лень придумывать pointfree версию
  simplePatch p [] = []
  simplePatch (ø ∷ xp) (x ∷ xx) = x ∷ simplePatch xp xx
  simplePatch (⊙ (f , t) ∷ xp) (x ∷ xx) = t ∷ simplePatch xp xx
  
  unite : ∀ {n} → (a b : Known n) → a ∥ b → Known n
  unite [] [] p = []
  unite (.ø ∷ xa) (.ø ∷ xb) (ø-ø p) = ø ∷ unite xa xb p
  unite (.ø ∷ xa) (.(⊙ b) ∷ xb) (ø-⊙ b p) = ⊙ b ∷ unite xa xb p
  unite (.(⊙ a) ∷ xa) (.ø ∷ xb) (⊙-ø a p) = ⊙ a ∷ unite xa xb p
  
  _≫_ : ∀ {n}{A} → (a b : Vec (A ⁇) n) → Vec (A ⁇) n
  [] ≫ [] = []
  (x ∷ xs) ≫ (ø ∷ ys) = x ∷ (xs ≫ ys)
  (x ∷ xs) ≫ (⊙ a ∷ ys) = ⊙ a ∷ (xs ≫ ys)

  data _⊂_ {A : Set} : ∀ {n} → Vec (A ⁇) n → Vec (A ⁇) n → Set where

  data Patch : {n : ℕ} → (from to : Known n) → Set where
    simple : ∀ {n} → (p : SimplePatch n) → Patch (dom p) (codom p)
    _⋀_ : ∀ {n}{f₁ t₁ f₂ t₂ : Known n}
      → (p : f₁ ∥ f₂) → Patch (unite f₁ f₂ p) (t₁ ≫ t₂)
    _⋙_ : ∀ {n}{f₁ t₁ f₂ t₂ : Known n}
      → (p : f₂ ⊂ t₁) → Patch (f₁ ≫ f₂) (t₁ ≫ t₂)
      
  {- тут я в очередной раз запутался -}

{- тут я решил попробовать сделать ядро VCS без доказательств,
   а доказательства прикрутить потом.
   Это выглядит разумно с той точки зрения, что, по идее, эта
   VCS должна в итоге стать программой. А в программе доказательства
   вырезаются -}
module VecLikePatch3 (A : Set) where
  open Data-Vec
  open Data-Maybe

  Data : ℕ → Set
  Data n = Vec A n

  SimplePatch : ℕ → Set
  SimplePatch n = Vec ((A × A) ⁇) n

  PatchRes : ℕ → Set
  PatchRes n = (Data n) ⁇

  data Patch : (n : ℕ) → Set where
    simple : ∀ {n} → SimplePatch n → Patch n
    _⋀_ : ∀ {n} → Patch n → Patch n → Patch n
    _⋙_ : ∀ {n} → Patch n → Patch n → Patch n

  patch : ∀ {n} → Patch n → Data n → PatchRes n
  patch (simple x) d = {!!}
  patch (p₁ ⋀ p₂) d = {!(patch p₁ ∘ patch p₂) d!}
  patch (p ⋙ p₁) d = {!!}

--  data Applyable : ∀ {n} → Patch n → Data n → Set where
--    ⋀-ap : ∀ {n}{x : Data n}{p₁ p₂ : Patch n}
--      → Applyable p₁ n → Applyable p₂ n → 
    
