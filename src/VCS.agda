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

  
  {-
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
    

module VecLikePatch4 (A : Set) where
  open Data-Vec
  open Data-Maybe

  Data : ℕ → Set
  Data n = Vec A n  
    
  Req : ℕ → Set
  Req n = Vec (A ⁇) n
  
  SimplePatch : ℕ → Set
  SimplePatch n = Vec ((A × A) ⁇) n
  
  data _∥_ : ∀ {n} → Req n → Req n → Set where
    []∥[] : [] ∥ []
    ⊙-ø : ∀ {n}{a}{r₁ r₂ : Req n}
      → r₁ ∥ r₂ → (⊙ a ∷ r₁) ∥ (ø ∷ r₂)
    ø-⊙ : ∀ {n}{a}{r₁ r₂ : Req n}
      → r₁ ∥ r₂ → (ø ∷ r₁) ∥ (⊙ a ∷ r₂)
    ø-ø : ∀ {n}{r₁ r₂ : Req n}
      → r₁ ∥ r₂ → (ø ∷ r₁) ∥ (ø ∷ r₂)
      
  unite : ∀ {n} → (r₁ : Req n) → (r₂ : Req n) → (r₁ ∥ r₂) → Req n
  unite .[] .[] []∥[] = []
  unite .(⊙ a ∷ r₁) .(ø ∷ r₂) (⊙-ø {n} {a} {r₁} {r₂} c) 
    = ⊙ a ∷ unite r₁ r₂ c
  unite .(ø ∷ r₁) .(⊙ a ∷ r₂) (ø-⊙ {n} {a} {r₁} {r₂} c) 
    = ⊙ a ∷ unite r₁ r₂ c
  unite .(ø ∷ r₁) .(ø ∷ r₂) (ø-ø {n} {r₁} {r₂} c) 
    = ø ∷ unite r₁ r₂ c
    
  _≫_ : ∀ {n} → (r₁ : Req n) → (r₂ : Req n) → Req n
  [] ≫ [] = []
  (r ∷ r₁) ≫ (ø ∷ r₂) = r ∷ (r₁ ≫ r₂)
  (_ ∷ r₁) ≫ (r ∷ r₂) = r ∷ (r₁ ≫ r₂)
  
  map : ∀ {n}{A B : Set} → (f : A → B) → Vec A n → Vec B n
  map f [] = []
  map f (x ∷ v) = f x ∷ map f v

  domₛ : ∀ {n} → SimplePatch n → Req n
  domₛ = map $ map⁇ projl
  
  codomₛ : ∀ {n} → SimplePatch n → Req n
  codomₛ = map $ map⁇ projr

  data _⟹_ : ∀ {n} → Req n → Req n → Set where
    Init : ∀ {n} (p : SimplePatch n) → (domₛ p) ⟹ (codomₛ p)
    _⋀_ : ∀ {n}{f₁ t₁ f₂ t₂ : Req n} 
      → (p₁ : f₁ ⟹ t₁) → (p₂ : f₂ ⟹ t₂)
      → (cf : f₁ ∥ f₂) → (ct : t₁ ∥ t₂)
      → (unite f₁ f₂ cf ⟹ unite t₁ t₂ ct)
    _⋙_ : ∀ {n}{f₁ t₁ f₂ t₂ : Req n}
      → (p₁ : f₁ ⟹ t₁) → (p₂ : f₂ ⟹ t₂)
      → (f₁ ≫ f₂) ⟹ (t₁ ≫ t₂)
      
  data _⊑_ : ∀ {n} → Req n → Data n → Set where
    empty : [] ⊑ []
    skip : ∀ {n} (r : Req n)(a : A)(d : Data n) 
      → (r ⊑ d) → (ø ∷ r) ⊑ (a ∷ d)
    get : ∀ {n} (r : Req n)(a : A)(d : Data n) 
      → (r ⊑ d) → (⊙ a ∷ r) ⊑ (a ∷ d)

  dom : ∀ {n}{r₁ r₂ : Req n} (p : r₁ ⟹ r₂) → Req n
  dom (Init p) = domₛ p
  dom (_⋀_ p p₁ cf ct) = dom p ≫ dom p₁
  dom (p ⋙ p₁) = dom p ≫ dom p₁

  codom : ∀ {n}{r₁ r₂ : Req n} (p : r₁ ⟹ r₂) → Req n
  codom (Init p) = codomₛ p
  codom (_⋀_ p p₁ cf ct) = codom p ≫ codom p₁
  codom (p ⋙ p₁) = codom p ≫ codom p₁

  unite-is-≫ : ∀ {n}{r₁ r₂ : Req n} → (p : r₁ ∥ r₂)
    → unite r₁ r₂ p ≡ r₁ ≫ r₂
  unite-is-≫ []∥[] = refl
  unite-is-≫ (⊙-ø p) rewrite unite-is-≫ p = refl
  unite-is-≫ (ø-⊙ p) rewrite unite-is-≫ p = refl
  unite-is-≫ (ø-ø p) rewrite unite-is-≫ p = refl

  lemma-1 : ∀ {n}{r₁ r₂ : Req n} (p : r₁ ⟹ r₂) → r₁ ≡ dom p
  lemma-1 (Init p) = refl
  lemma-1 (_⋀_ p p₁ cf ct) with dom p | lemma-1 p | dom p₁ | lemma-1 p₁ 
  lemma-1 (_⋀_ p p₁ cf ct) | _ | refl | _ | refl = unite-is-≫ cf
  lemma-1 (p ⋙ p₁) with dom p | lemma-1 p | dom p₁ | lemma-1 p₁
  lemma-1 (p ⋙ p₁) | w | refl | w₁ | refl = refl
  
  patchₛ : ∀ {n} (p : SimplePatch n) → (d : Data n) → (domₛ p ⊑ d) → Data n
  patchₛ [] [] empty = []
  patchₛ (ø ∷ p) (x₁ ∷ d) (skip .(map (map⁇ projl) p) .x₁ .d pp) = x₁ ∷ patchₛ p d pp
  patchₛ (⊙ (f , t) ∷ p) (.f ∷ d)  (get .(map (map⁇ projl) p) .f .d pp) 
    = t ∷ patchₛ p d pp
    
  ∥-comm : ∀ {n}{r₁ r₂ : Req n} → r₁ ∥ r₂ → r₂ ∥ r₁
  ∥-comm []∥[] = []∥[]
  ∥-comm (⊙-ø p) = ø-⊙ (∥-comm p)
  ∥-comm (ø-⊙ p) = ⊙-ø (∥-comm p)
  ∥-comm (ø-ø p) = ø-ø (∥-comm p)

  unite-comm : ∀ {n}{r₁ r₂ : Req n}(p : r₁ ∥ r₂)
    → unite r₁ r₂ p ≡ unite r₂ r₁ (∥-comm p)
  unite-comm []∥[] = refl
  unite-comm (⊙-ø p) rewrite unite-comm p = refl
  unite-comm (ø-⊙ p) rewrite unite-comm p = refl
  unite-comm (ø-ø p) rewrite unite-comm p = refl

  ⊑-div : ∀ {n}{f₁ f₂ : Req n}{d : Data n}
    (p : f₁ ∥ f₂) → (unite f₁ f₂ p) ⊑ d → f₁ ⊑ d
  ⊑-div []∥[] empty = empty
  ⊑-div (⊙-ø {n} {a} {r₁} {r₂} p) (get .(unite r₁ r₂ p) .a d u) = get r₁ a d (⊑-div p u)
  ⊑-div (ø-⊙ {n} {a} {r₁} {r₂} p) (get .(unite r₁ r₂ p) .a d u) = skip r₁ a d (⊑-div p u)
  ⊑-div (ø-ø {n} {r₁} {r₂} p) (skip .(unite r₁ r₂ p) a d u) = skip r₁ a d (⊑-div p u)
  
  drop : (n : ℕ)(f t : Req n)
    → (f' t' : A ⁇) → (f' ∷ f) ⟹ (t' ∷ t) → f ⟹ t
  drop n f t ø ø p = {!!} -- pattern match on `p` failed ⌢̈
  drop n f t ø (⊙ a) p = {!!}
  drop n f t (⊙ a) ø p = {!!}
  drop n f t (⊙ a) (⊙ a₁) p = {!!}


  patch : ∀ {n}{f t : Req n} → (f ⟹ t) → (d : Data n) → f ⊑ d → Data n
  patch (Init p) d pp = patchₛ p d pp
  patch (_⋀_ p₁ p₂ cf ct) [] pp = []
  patch {succ n} (_⋀_ {.(succ n)} {ø ∷ f₁} {ø ∷ t₁} {ø ∷ f₂} {ø ∷ t₂} p₁ p₂ (ø-ø cf) (ø-ø ct)) (x₂ ∷ d) (skip .(unite f₁ f₂ cf) .x₂ .d pp) = x₂ ∷ {!!}
  patch {succ n} (_⋀_ {.(succ n)} {ø ∷ f₁} {ø ∷ t₁} {ø ∷ f₂} {⊙ a ∷ t₂} p₁ p₂ (ø-ø cf) ct) (x₂ ∷ d) pp = {!!}
  patch {succ n} (_⋀_ {.(succ n)} {ø ∷ f₁} {⊙ a ∷ t₁} {ø ∷ f₂} {x₁ ∷ t₂} p₁ p₂ (ø-ø cf) ct) (x₂ ∷ d) pp = {!!} -- x₂ ∷ patch {n}{f₁}{f₂} {!!} d {!!}
  patch {succ n} (_⋀_ {.(succ n)} {ø ∷ f₁} {t₁} {⊙ a ∷ f₂} p₁ p₂ cf ct) (x₂ ∷ d) pp = {!!}
  patch {succ n} (_⋀_ {.(succ n)} {⊙ a ∷ f₁} {t₁} {x₁ ∷ f₂} p₁ p₂ cf ct) (x₂ ∷ d) pp = {!!}
  patch (p ⋙ p₁) d pp = {!!}

    {-
  _⟷_ : ∀ {n}{f₁ t₁ f₂ t₂ : Req n} → (f₁ ⟹ t₁) → (f₂ ⟹ t₂) → Set
  _⟷_ {n} p₁ p₂ = ∀ (x : Data n) → patch p₁ x ≡ patch p₂ x
    -}
  
  --⋀-is-⋙ : ∀ {n}{p₁ p₂ : Req n} → (c : Compatible p₁ p₂)
  --  → ((p₁ ⋀ p₂) c) ⟷ (p₁ ⋙ p₂)
  --⋀-is-⋙\gtr {n}{p₁}{p₂} c = ?

module VecLikePatchTransposed (A : Set) where

  open ℕ-Op
  open Data-Vec
  
  take : ∀ {A : Set}{m} → (n : ℕ) → Vec A (n + m) → Vec A n
  take zero v = []
  take (succ n) (x ∷ v) = x ∷ take n v
  
  drop : ∀ {A : Set}{m} → (n : ℕ) → Vec A (n + m) → Vec A m
  drop zero v = v
  drop (succ n) (_ ∷ v) = drop n v
  
  mutual
    data Patch : (n : ℕ) → Set where
      I : Patch (succ zero)
      _⇔_ : A → A → Patch (succ zero)
      _⊹_ : ∀ {n m} → Patch n → Patch m → Patch (n + m)
      _⋀_ : ∀ {n} → (p₁ : Patch n) → (p₂ : Patch n) 
        → (p₁ ∥ p₂) → Patch n
      _⋙_ : ∀ {n} → (p₁ : Patch n) → (p₂ : Patch n)
        → Patch n
    
    data _∥_ : {n : ℕ} → Patch n → Patch n → Set where
      I∥⋆ : (a b : A) → I ∥ (a ⇔ b)
      ⋆∥I : (a b : A) → (a ⇔ b) ∥ I
      I∥I : I ∥ I
      _|⊹|_ : ∀ {n m}{pₗ₁ pₗ₂ : Patch n}{pᵣ₁ pᵣ₂ : Patch m} 
        → pₗ₁ ∥ pₗ₂ → pᵣ₁ ∥ pᵣ₂ → (pₗ₁ ⊹ pᵣ₁) ∥ (pₗ₂ ⊹ pᵣ₂)
        -}

module VecLikePatchTransposedIndexed (A : Set) where

  open ℕ-Op
  open Data-Vec
  open Data-Maybe
  
  take : ∀ {A : Set}{m} → (n : ℕ) → Vec A (n + m) → Vec A n
  take zero v = []
  take (succ n) (x ∷ v) = x ∷ take n v
  
  drop : ∀ {A : Set}{m} → (n : ℕ) → Vec A (n + m) → Vec A m
  drop zero v = v
  drop (succ n) (_ ∷ v) = drop n v
  
  _++_ : ∀ {A : Set}{n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
  [] ++ v = v
  (x ∷ v₁) ++ v₂ = x ∷ v₁ ++ v₂

  [_] : ∀ {A : Set} → A → Vec A (succ zero)
  [ x ] = x ∷ []

  data _≫_≡_ {A : Set} : ∀ {n : ℕ} 
    → Vec (A ⁇) n → Vec (A ⁇) n → Vec (A ⁇) n → Set where
    []≫[] : [] ≫ [] ≡ []
    ø≫ø : ∀ {n}{v₁ v₂ v₃ : Vec (A ⁇) n} 
      → v₁ ≫ v₂ ≡ v₃ → (ø ∷ v₁) ≫ (ø ∷ v₂) ≡ (ø ∷ v₃)
    ⊙≫ø : ∀ {n}{v₁ v₂ v₃ : Vec (A ⁇) n}
      → (a : A) → (v₁ ≫ v₂ ≡ v₃)
      → (⊙ a ∷ v₁) ≫ (ø ∷ v₂) ≡ (⊙ a ∷ v₃)
    ✶≫⊙ : ∀ {n}{v₁ v₂ v₃ : Vec (A ⁇) n}
      → (l : A ⁇) → (r : A) → (v₁ ≫ v₂ ≡ v₃)
      → (l ∷ v₁) ≫ (⊙ r ∷ v₂) ≡ (⊙ r ∷ v₃)
      
  data _≪≫_≡_ {A : Set} : ∀ {n : ℕ}
    → Vec (A ⁇) n → Vec (A ⁇) n → Vec (A ⁇) n → Set where
    []≪≫[] : [] ≪≫ [] ≡ []
    ø≪≫ø : ∀ {n}{v₁ v₂ v₃ : Vec (A ⁇) n}
      → v₁ ≪≫ v₂ ≡ v₃ → (ø ∷ v₁) ≪≫ (ø ∷ v₂) ≡ (ø ∷ v₃)
    ⊙≪≫ø : ∀ {n}{v₁ v₂ v₃ : Vec (A ⁇) n}
      → (a : A) → v₁ ≪≫ v₂ ≡ v₃
      → (⊙ a ∷ v₁) ≪≫ (ø ∷ v₂) ≡ (⊙ a ∷ v₃)
    ø≪≫⊙ : ∀ {n}{v₁ v₂ v₃ : Vec (A ⁇) n}
      → (a : A) → v₁ ≪≫ v₂ ≡ v₃
      → (ø ∷ v₁) ≪≫ (⊙ a ∷ v₂) ≡ (⊙ a ∷ v₃)
    ⊙≪≫⊙ : ∀ {n}{v₁ v₂ v₃ : Vec (A ⁇) n}
      → (a : A) → v₁ ≪≫ v₂ ≡ v₃
      → (⊙ a ∷ v₁) ≪≫ (⊙ a ∷ v₂) ≡ (⊙ a ∷ v₃)

  data _∥_ {A : Set} : ∀ {n} → Vec (A ⁇) n → Vec (A ⁇) n → Set where
    []∥[] : [] ∥ []
    ø∥ø : ∀ {n}{v₁ v₂ : Vec (A ⁇) n} → v₁ ∥ v₂ → (ø ∷ v₁) ∥ (ø ∷ v₂)
    ⊙∥ø : ∀ {n}{v₁ v₂ : Vec (A ⁇) n} 
      → v₁ ∥ v₂ → (a : A) → (⊙ a ∷ v₁) ∥ (ø ∷ v₂)
    ø∥⊙ : ∀ {n}{v₁ v₂ : Vec (A ⁇) n}
      → v₁ ∥ v₂ → (a : A) → (ø ∷ v₁) ∥ (⊙ a ∷ v₂)
    ⊙∥⊙ : ∀ {n}{v₁ v₂ : Vec (A ⁇) n}
      → v₁ ∥ v₂ → (a : A) → (⊙ a ∷ v₁) ∥ (⊙ a ∷ v₂)
      
  data _⊏_ {A : Set} : ∀ {n} → Vec (A ⁇) n → Vec A n → Set where
    []⊏[] : [] ⊏ []
    ø⊏ : ∀ {n}{v : Vec (A ⁇) n}{x : Vec A n}
      → v ⊏ x → (a : A) → (ø ∷ v) ⊏ (a ∷ x)
    ⊙⊏ : ∀ {n}{v : Vec (A ⁇) n}{x : Vec A n}
      → v ⊏ x → (a : A) → (⊙ a ∷ v) ⊏ (a ∷ x)
      
  data _≃_ {A B : Set} : ∀ {n} → Vec (A ⁇) n → Vec (B ⁇) n → Set where
    []≃[] : [] ≃ []
    ø≃ø : ∀ {n}{v₁ : Vec (A ⁇) n}{v₂ : Vec (B ⁇) n}
      → v₁ ≃ v₂ → (ø ∷ v₁) ≃ (ø ∷ v₂)
    ⊙≃⊙ : ∀ {n}{v₁ : Vec (A ⁇) n}{v₂ : Vec (B ⁇) n}
      → v₁ ≃ v₂ → (a : A) → (b : B) → (⊙ a ∷ v₁) ≃ (⊙ b ∷ v₂)

  data _is_/_ {A B : Set} : ∀ {n} 
    → Vec A n → Vec A n → Vec (B ⁇) n → Set where
    []is[]/[] : [] is [] / []
    same/ø : ∀ {n}{v₁ v₂ : Vec A n}{v₃ : Vec (B ⁇) n}
      → v₁ is v₂ / v₃ → (a : A)
      → (a ∷ v₁) is (a ∷ v₂) / (ø ∷ v₃)
    diff/⊙ : ∀ {n}{v₁ v₂ : Vec A n}{v₃ : Vec (B ⁇) n}
      → v₁ is v₂ / v₃ → (a b : A) → (c : B)
      → (a ∷ v₁) is (b ∷ v₂) / (⊙ c ∷ v₃)
      
  -- Patch (what-should-be-before) (what-we-know-after)
  data Patch1 : A ⁇ → A ⁇ → Set where
    I : Patch1 ø ø
    _⇔_ : (from to : A) → Patch1 (⊙ from) (⊙ to)

  data Patch : {n : ℕ} → Vec (A ⁇) n → Vec (A ⁇) n → Set where
    --I : Patch [ ø ] [ ø ]
    --_⇔_ : (from to : A) → Patch [ ⊙ from ] [ ⊙ to ]
    --_∷+_ : ∀ {n}{f₁ t₁ : Vec (A ⁇) (succ zero)}{f₂ t₂ : Vec (A ⁇) n}
    --  → Patch f₁ t₁ → Patch f₂ t₂ → Patch (f₁ ++ f₂) (t₁ ++ t₂)
    O : Patch [] []
    _∷+_ : ∀ {n}{f₁ t₁ : A ⁇}{f₂ t₂ : Vec (A ⁇) n}
      → (p : Patch1 f₁ t₁) → (px : Patch f₂ t₂) 
      → Patch (f₁ ∷ f₂) (t₁ ∷ t₂)
    ⋀ : ∀ {n}{f₁ t₁ f₂ t₂ f₃ t₃ : Vec (A ⁇) n}
      → (f₁∥f₂ : f₁ ∥ f₂) → (t₁∥t₂ : t₁ ∥ t₂)
      → (f₃-ok : f₁ ≪≫ f₂ ≡ f₃) → (t₃-ok : t₁ ≪≫ t₂ ≡ t₃)
      → (p₁ : Patch f₁ t₁) → (p₂ : Patch f₂ t₂) 
      → Patch f₃ t₃
    ⋙ : ∀ {n}{f₁ t₁ f₂ t₂ f₃ t₃ : Vec (A ⁇) n} 
      → (f₃-ok : f₁ ≫ f₂ ≡ f₃) → (t₃-ok : t₁ ≫ t₂ ≡ t₃) → (can : t₁ ∥ f₂)
      → (p₁ : Patch f₁ t₁) → (p₂ : Patch f₂ t₂)
      → Patch f₃ t₃
      
  lem : ∀ {A : Set} {n : ℕ} {v₁ v₂ v₃ v₄ : Vec (A ⁇) n}
    → v₁ ≫ v₂ ≡ v₃ 
    → v₁ ≫ v₂ ≡ v₄ 
    → v₃ ≡ v₄
  lem []≫[] []≫[] = refl
  lem (ø≫ø p₁) (ø≫ø p₂) rewrite lem p₁ p₂ = refl
  lem (⊙≫ø a p₁) (⊙≫ø .a p₂) rewrite lem p₁ p₂ = refl
  lem (✶≫⊙ l r p₁) (✶≫⊙ .l .r p₂) rewrite lem p₁ p₂ = refl
  
  ∥→≪≫ : ∀ {n}{v₁ v₂ : Vec (A ⁇) n}
    → v₁ ∥ v₂ → Σ (Vec (A ⁇) n) λ v₃ → v₁ ≪≫ v₂ ≡ v₃
  ∥→≪≫ []∥[] = [] , []≪≫[]
  ∥→≪≫ (ø∥ø p) with ∥→≪≫ p
  ... | v₃ , pp = (ø ∷ v₃) , ø≪≫ø pp
  ∥→≪≫ (⊙∥ø p a) with ∥→≪≫ p 
  ... | v₃ , pp = (⊙ a ∷ v₃) , ⊙≪≫ø a pp
  ∥→≪≫ (ø∥⊙ p a) with ∥→≪≫ p 
  ... | v₃ , pp = (⊙ a ∷ v₃) , ø≪≫⊙ a pp
  ∥→≪≫ (⊙∥⊙ p a) with ∥→≪≫ p 
  ... | v₃ , pp = (⊙ a ∷ v₃) , ⊙≪≫⊙ a pp

  ≃-≪≫-lem : ∀ {n}{v₁₁ v₁₂ v₁₃ v₂₁ v₂₂ v₂₃ : Vec (A ⁇) n}
    → v₁₁ ≃ v₂₁ → v₁₂ ≃ v₂₂
    → v₁₁ ≪≫ v₁₂ ≡ v₁₃ → v₂₁ ≪≫ v₂₂ ≡ v₂₃
    → v₁₃ ≃ v₂₃
  ≃-≪≫-lem []≃[] []≃[] []≪≫[] []≪≫[] = []≃[]
  ≃-≪≫-lem (ø≃ø ≃1) (ø≃ø ≃2) (ø≪≫ø ≪≫1) (ø≪≫ø ≪≫2) 
    = ø≃ø (≃-≪≫-lem ≃1 ≃2 ≪≫1 ≪≫2)
  ≃-≪≫-lem (ø≃ø ≃1) (⊙≃⊙ ≃2 a b) (ø≪≫⊙ .a ≪≫1) (ø≪≫⊙ .b ≪≫2) 
    = ⊙≃⊙ (≃-≪≫-lem ≃1 ≃2 ≪≫1 ≪≫2) a b
  ≃-≪≫-lem (⊙≃⊙ ≃1 a b) (ø≃ø ≃2) (⊙≪≫ø .a ≪≫1) (⊙≪≫ø .b ≪≫2) 
    = ⊙≃⊙ (≃-≪≫-lem ≃1 ≃2 ≪≫1 ≪≫2) a b
  ≃-≪≫-lem (⊙≃⊙ ≃1 .a .b) (⊙≃⊙ ≃2 a b) (⊙≪≫⊙ .a ≪≫1) (⊙≪≫⊙ .b ≪≫2) 
    = ⊙≃⊙ (≃-≪≫-lem ≃1 ≃2 ≪≫1 ≪≫2) a b
    
  ≃-≫-lem : ∀ {n}{v₁₁ v₁₂ v₁₃ v₂₁ v₂₂ v₂₃ : Vec (A ⁇) n}
    → v₁₁ ≃ v₂₁ → v₁₂ ≃ v₂₂
    → v₁₁ ≫ v₁₂ ≡ v₁₃ → v₂₁ ≫ v₂₂ ≡ v₂₃
    → v₁₃ ≃ v₂₃
  ≃-≫-lem []≃[] []≃[] []≫[] []≫[] = []≃[]
  ≃-≫-lem (ø≃ø ≃1) (ø≃ø ≃2) (ø≫ø ≫1) (ø≫ø ≫2) 
    = ø≃ø (≃-≫-lem ≃1 ≃2 ≫1 ≫2)
  ≃-≫-lem (ø≃ø ≃1) (⊙≃⊙ ≃2 a b) (✶≫⊙ .ø .a ≫1) (✶≫⊙ .ø .b ≫2) 
    = ⊙≃⊙ (≃-≫-lem ≃1 ≃2 ≫1 ≫2) a b
  ≃-≫-lem (⊙≃⊙ ≃1 a b) (ø≃ø ≃2) (⊙≫ø .a ≫1) (⊙≫ø .b ≫2) 
    = ⊙≃⊙ (≃-≫-lem ≃1 ≃2 ≫1 ≫2) a b
  ≃-≫-lem (⊙≃⊙ ≃1 a b) (⊙≃⊙ ≃2 a₁ b₁) (✶≫⊙ .(⊙ a) .a₁ ≫1) (✶≫⊙ .(⊙ b) .b₁ ≫2) 
    = ⊙≃⊙ (≃-≫-lem ≃1 ≃2 ≫1 ≫2) a₁ b₁

  Patch-lem : ∀ {n}{f t : Vec (A ⁇) n}
    → (p : Patch f t) → f ≃ t
  Patch-lem O = []≃[]
  Patch-lem (I ∷+ p) = ø≃ø (Patch-lem p)
  Patch-lem ((from ⇔ to) ∷+ p) = ⊙≃⊙ (Patch-lem p) from to
  Patch-lem (⋀ f₁∥f₂ t₁∥t₂ f₃-ok t₃-ok p p₁) 
    = ≃-≪≫-lem (Patch-lem p) (Patch-lem p₁) f₃-ok t₃-ok
  Patch-lem (⋙ f₃-ok t₃-ok can p p₁) 
    = ≃-≫-lem (Patch-lem p) (Patch-lem p₁) f₃-ok t₃-ok

  patch : ∀ {n} {f t : Vec (A ⁇) n} (x : Vec A n)
    → f ⊏ x → (p : Patch f t) → Vec A n
  patch [] []⊏[] O = []
  patch (x ∷ xs) (ø⊏ pf .x) (I ∷+ px) = x ∷ patch xs pf px
  patch (x ∷ xs) (⊙⊏ pf .x) ((.x ⇔ to) ∷+ px) = to ∷ patch xs pf px
  patch x pf (⋀ x₁ x₂ x₃ x₄ p p₁) = {!!}
  patch x pf (⋙ f₃-ok t₃-ok t₁∥f₂ p₁ p₂) = 
    patch (patch x {!!} p₁) {!!} p₂

  ∥-lem-1 : ∀ {n}{v₁ v₂ v₃ : Vec (A ⁇) n}{x : Vec A n} 
    → v₁ ≪≫ v₂ ≡ v₃ → v₃ ⊏ x → v₁ ⊏ x
  ∥-lem-1 []≪≫[] []⊏[] = []⊏[]
  ∥-lem-1 (ø≪≫ø p1) (ø⊏ p2 a) = ø⊏ (∥-lem-1 p1 p2) a
  ∥-lem-1 (⊙≪≫ø a p1) (⊙⊏ p2 .a) = ⊙⊏ (∥-lem-1 p1 p2) a
  ∥-lem-1 (ø≪≫⊙ a p1) (⊙⊏ p2 .a) = ø⊏ (∥-lem-1 p1 p2) a
  ∥-lem-1 (⊙≪≫⊙ a p1) (⊙⊏ p2 .a) = ⊙⊏ (∥-lem-1 p1 p2) a
  
  ≪≫-sym : ∀ {n}{v₁ v₂ v₃ : Vec (A ⁇) n}
    → v₁ ≪≫ v₂ ≡ v₃ → v₂ ≪≫ v₁ ≡ v₃
  ≪≫-sym []≪≫[] = []≪≫[]
  ≪≫-sym (ø≪≫ø p) = ø≪≫ø (≪≫-sym p)
  ≪≫-sym (⊙≪≫ø a p) = ø≪≫⊙ a (≪≫-sym p)
  ≪≫-sym (ø≪≫⊙ a p) = ⊙≪≫ø a (≪≫-sym p)
  ≪≫-sym (⊙≪≫⊙ a p) = ⊙≪≫⊙ a (≪≫-sym p)

  
  vpatch-lem-1 : ∀ {n}{x y : Vec A n}{v₁ v₂ v₃ : Vec (A ⁇) n}
    → v₁ ≪≫ v₂ ≡ v₃ → v₃ ⊏ x
    → x is y / v₁ → v₂ ⊏ y
  vpatch-lem-1 []≪≫[] []⊏[] []is[]/[] = []⊏[]
  vpatch-lem-1 (ø≪≫ø ≪≫) (ø⊏ ⊏1 a) (same/ø is/ .a) 
    = ø⊏ (vpatch-lem-1 ≪≫ ⊏1 is/) a
  vpatch-lem-1 (⊙≪≫ø a ≪≫) (⊙⊏ ⊏1 .a) (diff/⊙ is/ .a b .a) 
    = ø⊏ (vpatch-lem-1 ≪≫ ⊏1 is/) b
  vpatch-lem-1 (ø≪≫⊙ a ≪≫) (⊙⊏ ⊏1 .a) (same/ø is/ .a) 
    = ⊙⊏ (vpatch-lem-1 ≪≫ ⊏1 is/) a
  {- FIXME вот тут всё сломалось из-за ⊙∥⊙ -}
  vpatch-lem-1 (⊙≪≫⊙ a ≪≫) (⊙⊏ ⊏1 .a) (diff/⊙ is/ .a b .a) 
    = {!!}

  vpatch : ∀ {n} {f t : Vec (A ⁇) n} (x : Vec A n)
    → f ⊏ x → (p : Patch f t) → Σ (Vec A n) λ y → (t ⊏ y) × (x is y / f)
  vpatch [] []⊏[] O = [] , []⊏[] , []is[]/[]
  vpatch (x ∷ xs) (ø⊏ pf .x) (I ∷+ px) with vpatch xs pf px 
  ... | tail , p1 , p2 = (x ∷ tail) , ø⊏ p1 x , same/ø p2 x
  vpatch (x ∷ xs) (⊙⊏ pf .x) ((.x ⇔ to) ∷+ px) with vpatch xs pf px
  ... | tail , p1 , p2 = (to ∷ tail) , ⊙⊏ p1 to , diff/⊙ p2 x to x
  vpatch x pf (⋀ f₁∥f₂ t₁∥t₂ f₃-ok t₃-ok p₁ p₂) with vpatch x (∥-lem-1 f₃-ok pf) p₁ 
  ... | s₁ , p1 , p2 with vpatch s₁ {!!} {-(vpatch-lem-1 f₃-ok pf p2)-} p₂
  ... | s₂ , p3 , p4 = {!!}
  vpatch x pf (⋙ f₃-ok t₃-ok can p p₁) = {!!}

  {-
  vpatch : ∀ {n} {f t : Vec (A ⁇) n} (x : Vec A n)
    → f ⊏ x → (p : Patch f t) → Σ (Vec A n) λ y → t ⊏ y
  vpatch [] []⊏[] O = [] , []⊏[]
  vpatch (x ∷ xs) (ø⊏ pf .x) (I ∷+ px) with vpatch xs pf px
  ... | tail , p = (x ∷ tail) , ø⊏ p x
  vpatch (x ∷ xs) (⊙⊏ pf .x) ((.x ⇔ to) ∷+ px) with vpatch xs pf px
  ... | tail , p = (to ∷ tail) , ⊙⊏ p to
  vpatch x pf (⋀ {f₂ = f₂}f₁∥f₂ t₁∥t₂ f₃-ok t₃-ok p₁ p₂) with vpatch x (∥-lem-1 f₃-ok pf) p₁
  ... | s₁ , ppp with vpatch s₁ {!!} p₂
  ... | s₂ , pppp = {!!} 
  vpatch x pf (⋙ f₃-ok t₃-ok can p₁ p₂) with vpatch x {!!} p₁
  ... | s₁ , ppp with vpatch s₁ {!!} p₂
  ... | s₂ , pppp = {!!}
  -}

      {-
  patch : ∀ {n} {f t : Vec (A ⁇) n} (x : Vec A n)
    → f ⊏ x → (p : Patch f t) → Vec A n
  patch [] []⊏[] _ = []
  patch (x ∷ []) pf I = x ∷ []
  patch (x ∷ []) (⊙⊏ pf .x) (.x ⇔ to) = to ∷ []
  patch (x ∷ xs) pf (I ∷+ px) = {!!}
  patch (x ∷ xs) pf ((from ⇔ to) ∷+ px) = {!!}
  patch (x ∷ xs) pf ((p ∷+ p₁) ∷+ px) = {!!}
  patch (x ∷ xs) pf (⋀ x₁ x₂ x₃ x₄ p p₁ ∷+ px) = {!!}
  patch (x ∷ xs) pf (⋙ x₁ x₂ x₃ p p₁ ∷+ px) = {!!}
--    patch (x ∷ []) {!!} p ++ patch xs {!!} px 
  patch (x ∷ xs) pf (⋀ x₁ x₂ x₃ x₄ p p₁) = {!!}
  patch (x ∷ xs) pf (⋙ x₁ x₂ x₃ p p₁) = {!!}
    -}

module VecLikePatchTransposed2 (A : Set) where
  
  mutual
    data Patch : (n : ℕ) → Set where
      [] : Patch zero
      ⟨_⇒_⟩∷_ : ∀ {n} → A → A → Patch n → Patch (succ n)
      I∷_ : ∀ {n} → Patch n → Patch (succ n)
      _⋀_ : ∀ {n} → (p₁ : Patch n) → (p₂ : Patch n)
        → p₁ ∥ p₂ → Patch n
    
    data _∥_ : {n : ℕ} → Patch n → Patch n → Set where
      

{-
module VecLikePatchTransposedIndexed2 (A : Set) where
  
  open Data-Maybe

  module SingleCellPatch where
    
    data _≫1_≡_ {A : Set} : A ⁇ → A ⁇ → A ⁇ → Set where
      ø≫1ø : ø ≫1 ø ≡ ø
      ⊙≫1ø : (a : A) → ⊙ a ≫1 ø ≡ ⊙ a
      ✶≫1⊙ : (a : A ⁇) (b : A) → a ≫1 ⊙ b ≡ ⊙ b
      
    data _≪≫1_≡_ {A : Set} : A ⁇ → A ⁇ → A ⁇ → Set where
      ø≪≫1ø : ø ≪≫1 ø ≡ ø
      ⊙≪≫1ø : (a : A) → ⊙ a ≪≫1 ø ≡ ⊙ a
      ø≪≫1⊙ : (a : A) → ø ≪≫1 ⊙ a ≡ ⊙ a
      
    data _∥1_ {A : Set} : A ⁇ → A ⁇ → Set where
      ø∥1ø : ø ∥1 ø
      ⊙∥1ø : (a : A) → ⊙ a ∥1 ø
      ø∥1⊙ : (a : A) → ø ∥1 ⊙ a
      
    data _=∥1_ {A : Set} : A ⁇ → A ⁇ → Set where
      from∥ : {a b : A ⁇} → a ∥1 b → a =∥1 b
      ⊙=∥1⊙ : (a : A) → ⊙ a =∥1 ⊙ a
    
    data _⊏1_ {A : Set} : A ⁇ → A → Set where
      ø⊏1 : (a : A) → ø ⊏1 a
      ⊙⊏1 : (a : A) → ⊙ a ⊏1 a
      
    data _is1_/_ {A B : Set} : (a b : A) (c : B ⁇) → Set where
      same1/ø : (a : A) → a is1 a / ø
      diff1/⊙ : (a b : A) (c : B) → a is1 b / ⊙ c
      
    data Patch1 : A ⁇ → A ⁇ → Set where
      I : Patch1 ø ø
      _⇔_ : (from to : A) → Patch1 (⊙ from) (⊙ to)
      ∧1 : ∀ {f₁ t₁ f₂ t₂ f₃ t₃ : A ⁇}
        → (f₁∥f₂ : f₁ ∥1 f₂) → (t₁∥t₂ : t₁ ∥1 t₂)
        → (f₃-ok : f₁ ≪≫1 f₂ ≡ f₃) → (t₃-ok : t₁ ≪≫1 t₂ ≡ t₃)
        → (p₁ : Patch1 f₁ t₁) → (p₂ : Patch1 f₂ t₂)
        → Patch1 f₃ t₃
      ⋙1 : ∀ {f₁ t₁ f₂ t₂ f₃ t₃ : A ⁇}
        → (can : t₁ =∥1 f₂) -- очень плохо
        → (f₃-ok : f₁ ≫1 f₂ ≡ f₃) → (t₃-ok : t₁ ≫1 t₂ ≡ t₃)
        → (p₁ : Patch1 f₁ t₁) → (p₂ : Patch1 f₂ t₂)
        → Patch1 f₃ t₃
        
    data _≃1_ {A B : Set} : A ⁇ → B ⁇ → Set where
      ø≃1ø : ø ≃1 ø
      ⊙≃1⊙ : (a : A) (b : B) → ⊙ a ≃1 ⊙ b
      
    ≃-≪≫-lem : ∀ {a1 a2 a3 b1 b2 b3 : A ⁇}
      → a1 ≪≫1 a2 ≡ a3 → b1 ≪≫1 b2 ≡ b3
      → a1 ≃1 b1 → a2 ≃1 b2 → a3 ≃1 b3
    ≃-≪≫-lem ø≪≫1ø ø≪≫1ø ø≃1ø ø≃1ø = ø≃1ø
    ≃-≪≫-lem (⊙≪≫1ø a) (⊙≪≫1ø a₁) (⊙≃1⊙ .a .a₁) ø≃1ø = ⊙≃1⊙ a a₁
    ≃-≪≫-lem (ø≪≫1⊙ a) (ø≪≫1⊙ a₁) ø≃1ø (⊙≃1⊙ .a .a₁) = ⊙≃1⊙ a a₁
    
    ≃-≫-lem : ∀ {a1 a2 a3 b1 b2 b3 : A ⁇}
      → a1 ≫1 a2 ≡ a3 → b1 ≫1 b2 ≡ b3
      → a1 ≃1 b1 → a2 ≃1 b2 → a3 ≃1 b3
    ≃-≫-lem ø≫1ø ø≫1ø ø≃1ø ø≃1ø = ø≃1ø
    ≃-≫-lem (⊙≫1ø a) (⊙≫1ø a₁) (⊙≃1⊙ .a .a₁) ø≃1ø = ⊙≃1⊙ a a₁
    ≃-≫-lem (✶≫1⊙ .ø b) (✶≫1⊙ .ø b₁) ø≃1ø (⊙≃1⊙ .b .b₁) = ⊙≃1⊙ b b₁
    ≃-≫-lem (✶≫1⊙ .(⊙ a) b) (✶≫1⊙ .(⊙ b₂) b₁) (⊙≃1⊙ a b₂) (⊙≃1⊙ .b .b₁) = ⊙≃1⊙ b b₁
    
    Patch1-lem : ∀ {f t} → Patch1 f t → f ≃1 t
    Patch1-lem I = ø≃1ø
    Patch1-lem (from ⇔ to) = ⊙≃1⊙ from to
    Patch1-lem (∧1 f₁∥f₂ t₁∥t₂ f₃-ok t₃-ok p p₁) =
      ≃-≪≫-lem f₃-ok t₃-ok (Patch1-lem p) (Patch1-lem p₁)
    Patch1-lem (⋙1 can f₃-ok t₃-ok p p₁) = 
      ≃-≫-lem f₃-ok t₃-ok (Patch1-lem p) (Patch1-lem p₁)
        
    vpatch-lem-1 : ∀ {a b c : A ⁇}{x : A}
      → a ≪≫1 b ≡ c → c ⊏1 x → a ⊏1 x
    vpatch-lem-1 ø≪≫1ø (ø⊏1 x) = ø⊏1 x
    vpatch-lem-1 {x = x} (⊙≪≫1ø .x) (⊙⊏1 .x) = ⊙⊏1 x
    vpatch-lem-1 {x = x} (ø≪≫1⊙ .x) (⊙⊏1 .x) = ø⊏1 x
    
    vpatch-lem-2 : ∀ {a b c : A ⁇}{x : A}
      → a ≫1 b ≡ c → c ⊏1 x → a ⊏1 x
    vpatch-lem-2 = {!!}

    vpatch : {f t : A ⁇} (x : A)
      → f ⊏1 x → (p : Patch1 f t) → Σ A λ y → (t ⊏1 y) × (x is1 y / f)
    vpatch x pf I = x , pf , same1/ø x
    vpatch x (⊙⊏1 .x) (.x ⇔ to) = to , ⊙⊏1 to , diff1/⊙ x to x
    vpatch x pf (∧1 f₁∥f₂ t₁∥t₂ f₃-ok t₃-ok p p₁) with vpatch x (vpatch-lem-1 f₃-ok pf) p 
    vpatch .s₁ pf (∧1 ø∥1ø ø∥1ø ø≪≫1ø ø≪≫1ø p p₁) | s₁ , ø⊏1 .s₁ , same1/ø .s₁ = s₁ , pf , same1/ø s₁
    vpatch .s₁ (ø⊏1 .s₁) (∧1 ø∥1ø (ø∥1⊙ a) ø≪≫1ø (ø≪≫1⊙ .a) p p₁) | s₁ , ø⊏1 .s₁ , same1/ø .s₁ with Patch1-lem p₁
    vpatch .s₁ (ø⊏1 .s₁) (∧1 ø∥1ø (ø∥1⊙ a) ø≪≫1ø (ø≪≫1⊙ .a) p p₁) | s₁ , ø⊏1 .s₁ , same1/ø .s₁ | ()
    vpatch .s₁ pf (∧1 (ø∥1⊙ a) ø∥1ø f₃-ok t₃-ok p p₁) | s₁ , ø⊏1 .s₁ , same1/ø .s₁ with Patch1-lem p₁
    ... | ()
    vpatch .s₁ pf (∧1 (ø∥1⊙ a) (ø∥1⊙ a₁) (ø≪≫1⊙ .a) (ø≪≫1⊙ .a₁) p p₁) | s₁ , ø⊏1 .s₁ , same1/ø .s₁ = a₁ , ⊙⊏1 a₁ , diff1/⊙ s₁ a₁ a
    vpatch x pf (∧1 (⊙∥1ø .c) ø∥1ø (⊙≪≫1ø .c) ø≪≫1ø p p₁) | s₁ , ø⊏1 .s₁ , diff1/⊙ .x .s₁ c = c , ø⊏1 c , diff1/⊙ x c c
    vpatch x pf (∧1 (⊙∥1ø .c) (ø∥1⊙ a) (⊙≪≫1ø .c) (ø≪≫1⊙ .a) p p₁) | s₁ , ø⊏1 .s₁ , diff1/⊙ .x .s₁ c = a , ⊙⊏1 a , diff1/⊙ x a c
    vpatch .s₁ pf (∧1 ø∥1ø (⊙∥1ø .s₁) ø≪≫1ø (⊙≪≫1ø .s₁) p p₁) | s₁ , ⊙⊏1 .s₁ , same1/ø .s₁ with Patch1-lem p
    ... | ()
    vpatch .s₁ pf (∧1 (ø∥1⊙ a) (⊙∥1ø .s₁) (ø≪≫1⊙ .a) (⊙≪≫1ø .s₁) p p₁) | s₁ , ⊙⊏1 .s₁ , same1/ø .s₁ with Patch1-lem p
    ... | ()
    vpatch x pf (∧1 (⊙∥1ø .c) (⊙∥1ø .s₁) (⊙≪≫1ø .c) (⊙≪≫1ø .s₁) p p₁) | s₁ , ⊙⊏1 .s₁ , diff1/⊙ .x .s₁ c = s₁ , ⊙⊏1 s₁ , diff1/⊙ x s₁ c
    vpatch x pf (⋙1 can f₃-ok t₃-ok p p₁) with vpatch x {!!} p
    ... | s₁ , p1 , p2 = {!!}

    -}





