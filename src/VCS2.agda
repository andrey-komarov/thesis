module VCS2 where

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

module SimpleWithFunctions (A : Set) where
  
  open Data-Vec
  open ≡-Prop

  Form : ℕ → Set
  Form = Vec Bool 

  data Patch : ∀ {n} → Form n → Set where
    O : Patch []
    ⊥∷ : ∀ {n}{f : Form n} → Patch f → Patch (false ∷ f)
    ⟨_⇒_⟩∷_ : ∀ {n}{f : Form n} → (from to : A) → Patch f → Patch (true ∷ f)

  data _∥_ : ∀ {n} → Form n → Form n → Set where
    []∥[] : [] ∥ []
    ⊥∥⊥ : ∀ {n}{f₁ f₂ : Form n} → f₁ ∥ f₂ → (false ∷ f₁) ∥ (false ∷ f₂)
    ⊤∥⊥ : ∀ {n}{f₁ f₂ : Form n} → f₁ ∥ f₂ → (true ∷ f₁) ∥ (false ∷ f₂)
    ⊥∥⊤ : ∀ {n}{f₁ f₂ : Form n} → f₁ ∥ f₂ → (false ∷ f₁) ∥ (true ∷ f₂)
    
  data _⊏_ : ∀ {n}{f : Form n} → Patch f → Vec A n → Set where
    []⊏[] : O ⊏ []
    ⊥⊏ : ∀ {n}{f : Form n}{p : Patch f}{v : Vec A n}
      → (a : A) → p ⊏ v → (⊥∷ p) ⊏ (a ∷ v)
    ⊤⊏ : ∀ {n}{f : Form n}{p : Patch f}{v : Vec A n}
      → (a b : A) → p ⊏ v → (⟨ a ⇒ b ⟩∷ p) ⊏ (a ∷ v)

  patch : ∀ {n}{f : Form n} → (p : Patch f) → (x : Vec A n) → p ⊏ x → Vec A n
  patch O [] []⊏[] = []
  patch (⊥∷ p) (x ∷ xs) (⊥⊏ .x pf) = x ∷ patch p xs pf
  patch (⟨ .x ⇒ to ⟩∷ p) (x ∷ xs) (⊤⊏ .x .to pf) = to ∷ patch p xs pf
  
  _^_ : ∀ {n} (f₁ f₂ : Form n) → f₁ ∥ f₂ → Form n
  _^_ [] [] []∥[] = []
  _^_ (.false ∷ xs) (.false ∷ ys) (⊥∥⊥ p) = false ∷ (xs ^ ys) p
  _^_ (.true ∷ xs) (.false ∷ ys) (⊤∥⊥ p) = true ∷ (xs ^ ys) p
  _^_ (.false ∷ xs) (.true ∷ ys) (⊥∥⊤ p) = true ∷ (xs ^ ys) p

  unite : ∀ {n} {f₁ f₂ : Form n} → f₁ ∥ f₂ → Form n
  unite {n} {f₁} {f₂} p = (f₁ ^ f₂) p

  _⋀_ : ∀ {n} {f₁ f₂ : Form n} (p₁ : Patch f₁) (p₂ : Patch f₂)
    → (f₁∥f₂ : f₁ ∥ f₂) → Patch (unite f₁∥f₂)
  _⋀_ O O []∥[] = O
  _⋀_ (⊥∷ p₁) (⊥∷ p₂) (⊥∥⊥ f₁∥f₂) = ⊥∷ ((p₁ ⋀ p₂) f₁∥f₂)
  _⋀_ (⟨ from ⇒ to ⟩∷ p₁) (⊥∷ p₂) (⊤∥⊥ f₁∥f₂) = 
    ⟨ from ⇒ to ⟩∷ ((p₁ ⋀ p₂) f₁∥f₂)
  _⋀_ (⊥∷ p₁) (⟨ from ⇒ to ⟩∷ p₂) (⊥∥⊤ f₁∥f₂) = 
    ⟨ from ⇒ to ⟩∷ ((p₁ ⋀ p₂) f₁∥f₂)
  
  patch-lem : ∀ {n}{f₁ f₂ : Form n} 
    → (x : Vec A n) → (p : f₁ ∥ f₂)
    → (p₁ : Patch f₁) → (p₂ : Patch f₂)
    → p₁ ⊏ x → p₂ ⊏ x
    → ((p₁ ⋀ p₂) p ⊏ x)
  patch-lem [] []∥[] O O []⊏[] []⊏[] = []⊏[]
  patch-lem (x ∷ xs) (⊥∥⊥ p) (⊥∷ p₁) (⊥∷ p₂) (⊥⊏ .x p₁⊏x) (⊥⊏ .x p₂⊏x) = 
    ⊥⊏ x (patch-lem xs p p₁ p₂ p₁⊏x p₂⊏x)
  patch-lem (x ∷ xs) (⊤∥⊥ p) (⟨ .x ⇒ to ⟩∷ p₁) (⊥∷ p₂) (⊤⊏ .x .to p₁⊏x) (⊥⊏ .x p₂⊏x) = 
    ⊤⊏ x to (patch-lem xs p p₁ p₂ p₁⊏x p₂⊏x)
  patch-lem (x ∷ xs) (⊥∥⊤ p) (⊥∷ p₁) (⟨ .x ⇒ to ⟩∷ p₂) (⊥⊏ .x p₁⊏x) (⊤⊏ .x .to p₂⊏x) = 
    ⊤⊏ x to (patch-lem xs p p₁ p₂ p₁⊏x p₂⊏x)
    
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

  {- p₁ ⟷ p₂ ─ p₁ операционно эквивалентен p₂ -}
  _⟷_ : ∀ {n}{f₁ f₂ : Form n} 
    → (p₁ : Patch f₁) → (p₂ : Patch f₂) → Set
  _⟷_ {n} p₁ p₂ = ∀ (x : Vec A n) → (p₁⊏x : p₁ ⊏ x) → (p₂⊏x : p₂ ⊏ x) 
    → patch p₁ x p₁⊏x ≡ patch p₂ x p₂⊏x

  lemma-1 : O ⟷ O
  lemma-1 .[] []⊏[] []⊏[] = refl

  ⋀-comm : ∀ {n}{f₁ f₂ : Form n}
    → (f₁∥f₂ : f₁ ∥ f₂)
    → (p₁ : Patch f₁) → (p₂ : Patch f₂)
    → ((p₁ ⋀ p₂) f₁∥f₂) ⟷ ((p₂ ⋀ p₁) (∥-comm f₁∥f₂))
  ⋀-comm []∥[] O O [] []⊏[] []⊏[] = refl
  ⋀-comm (⊥∥⊥ f₁∥f₂) (⊥∷ p₁) (⊥∷ p₂) (x ∷ x₁) (⊥⊏ .x p₁⊏x) (⊥⊏ .x p₂⊏x)
    rewrite ⋀-comm f₁∥f₂ p₁ p₂ x₁ p₁⊏x p₂⊏x = refl
  ⋀-comm (⊤∥⊥ f₁∥f₂) (⟨ .x ⇒ to ⟩∷ p₁) (⊥∷ p₂) (x ∷ x₁) (⊤⊏ .x .to p₁⊏x) (⊤⊏ .x .to p₂⊏x) 
    rewrite ⋀-comm f₁∥f₂ p₁ p₂ x₁ p₁⊏x p₂⊏x = refl
  ⋀-comm (⊥∥⊤ f₁∥f₂) (⊥∷ p₁) (⟨ .x ⇒ to ⟩∷ p₂) (x ∷ x₁) (⊤⊏ .x .to p₁⊏x) (⊤⊏ .x .to p₂⊏x) 
    rewrite ⋀-comm f₁∥f₂ p₁ p₂ x₁ p₁⊏x p₂⊏x = refl

  ⋀-assoc : ∀ {n}{f₁ f₂ f₃ : Form n} 
    → (f₁∥f₂ : f₁ ∥ f₂) → (f₂∥f₃ : f₂ ∥ f₃) → (f₁∥f₃ : f₁ ∥ f₃)
    → (p₁ : Patch f₁) → (p₂ : Patch f₂) → (p₃ : Patch f₃)
    → (((p₁ ⋀ p₂) f₁∥f₂) ⋀ p₃) (lemma-∥-unite f₁∥f₂ f₂∥f₃ f₁∥f₃) ⟷ 
      (p₁ ⋀ ((p₂ ⋀ p₃) f₂∥f₃)) 
        (∥-comm (lemma-∥-unite f₂∥f₃ (∥-comm f₁∥f₃) (∥-comm f₁∥f₂)))
  ⋀-assoc []∥[] []∥[] []∥[] O O O [] []⊏[] []⊏[] = refl
  ⋀-assoc (⊥∥⊥ f₁∥f₂) (⊥∥⊥ f₂∥f₃) (⊥∥⊥ f₁∥f₃) (⊥∷ p₁) (⊥∷ p₂) (⊥∷ p₃) (x ∷ xs) (⊥⊏ .x p₁⊏x) (⊥⊏ .x p₂⊏x) rewrite
    ⋀-assoc f₁∥f₂ f₂∥f₃ f₁∥f₃ p₁ p₂ p₃ xs p₁⊏x p₂⊏x = refl
  ⋀-assoc (⊥∥⊥ f₁∥f₂) (⊥∥⊤ f₂∥f₃) (⊥∥⊤ f₁∥f₃) (⊥∷ p₁) (⊥∷ p₂) (⟨ .x ⇒ to ⟩∷ p₃) (x ∷ xs) (⊤⊏ .x .to p₁⊏x) (⊤⊏ .x .to p₂⊏x) rewrite
    ⋀-assoc f₁∥f₂ f₂∥f₃ f₁∥f₃ p₁ p₂ p₃ xs p₁⊏x p₂⊏x = refl
  ⋀-assoc (⊤∥⊥ f₁∥f₂) (⊥∥⊥ f₂∥f₃) (⊤∥⊥ f₁∥f₃) (⟨ .x ⇒ to ⟩∷ p₁) (⊥∷ p₂) (⊥∷ p₃) (x ∷ xs) (⊤⊏ .x .to p₁⊏x) (⊤⊏ .x .to p₂⊏x) rewrite
    ⋀-assoc f₁∥f₂ f₂∥f₃ f₁∥f₃ p₁ p₂ p₃ xs p₁⊏x p₂⊏x = refl
  ⋀-assoc (⊤∥⊥ f₁∥f₂) (⊥∥⊤ f₂∥f₃) () p₁ p₂ p₃ x p₁⊏x p₂⊏x
  ⋀-assoc (⊥∥⊤ f₁∥f₂) (⊤∥⊥ f₂∥f₃) (⊥∥⊥ f₁∥f₃) (⊥∷ p₁) (⟨ .x ⇒ to ⟩∷ p₂) (⊥∷ p₃) (x ∷ xs) (⊤⊏ .x .to p₁⊏x) (⊤⊏ .x .to p₂⊏x) rewrite
    ⋀-assoc f₁∥f₂ f₂∥f₃ f₁∥f₃ p₁ p₂ p₃ xs p₁⊏x p₂⊏x = refl
    
  vec-strip : ∀ {n} {a₁ a₂ : A} {ax₁ ax₂ : Vec A n}
    → (a₁ ∷ ax₁) ≡ (a₂ ∷ ax₂) → ax₁ ≡ ax₂
  vec-strip refl = refl
  
  {- Эти четыре леммы для ⟷-isoshape -}
  ⟷-strip-⊥⊥ : ∀ {n}{f₁ f₂ : Form n}
    → {p₁ : Patch f₁} → {p₂ : Patch f₂}
    → ⊥∷ p₁ ⟷ ⊥∷ p₂ → p₁ ⟷ p₂
  ⟷-strip-⊥⊥ {zero} ⊥∷p₁⟷⊥∷p₂ [] []⊏[] []⊏[] = refl
  ⟷-strip-⊥⊥ {succ n} ⊥∷p₁⟷⊥∷p₂ (x ∷ xs) p₁⊏x p₂⊏x with
    ⊥∷p₁⟷⊥∷p₂ (x ∷ x ∷ xs) (⊥⊏ x p₁⊏x) (⊥⊏ x p₂⊏x)
  ... | ppp = vec-strip ppp
  
  {- Но тут ничего не получилось из-за патчей, говорящих, что они 
     поменяют букву, но на самом деле ничего не делают -}
  {-
  ⟷-strip-⊥⊤ : ∀ {n}{f₁ f₂ : Form n}
    → {p₁ : Patch f₁} → {p₂ : Patch f₂}
    → (from to : A)
    → ¬ ( ⊥∷ p₁ ⟷ ⟨ from ⇒ to ⟩∷ p₂)
  ⟷-strip-⊥⊤ {zero} {.[]} {.[]} {O} {O} from to p₁⟷p₂ with
    p₁⟷p₂ (from ∷ []) (⊥⊏ from []⊏[]) (⊤⊏ from to []⊏[])
  ⟷-strip-⊥⊤ {zero} {.[]} {.[]} {O} {O} .to to p₁⟷p₂ | refl = {!!}
  ⟷-strip-⊥⊤ {succ n} from to p₁⟷p₂ = {!!}
  -}

  {- Не судьба -}
  {-
  ⟷-isoshape : ∀ {n}{f₁ f₂ : Form n}
    → {p₁ : Patch f₁} → {p₂ : Patch f₂}
    → p₁ ⟷ p₂ → f₁ ≡ f₂
  ⟷-isoshape {zero} {[]} {[]} p₁⟷p₂ = refl
  ⟷-isoshape {succ n} {.false ∷ f₁} {.false ∷ f₂} {⊥∷ p₁} {⊥∷ p₂} p₁⟷p₂ rewrite
    ⟷-isoshape (⟷-strip-⊥⊥ p₁⟷p₂) = refl
  ⟷-isoshape {succ n} {.false ∷ f₁} {.true ∷ f₂} {⊥∷ p₁} {⟨ from ⇒ to ⟩∷ p₂} p₁⟷p₂ = ⊥-elim (⟷-strip-⊥⊤ from to p₁⟷p₂)
  ⟷-isoshape {succ n} {.true ∷ f₁} {.false ∷ f₂} {⟨ from ⇒ to ⟩∷ p₁} {⊥∷ p₂} p₁⟷p₂ = {!!}
  ⟷-isoshape {succ n} {.true ∷ f₁} {.true ∷ f₂} {⟨ from ⇒ to ⟩∷ p₁} {⟨ from₁ ⇒ to₁ ⟩∷ p₂} p₁⟷p₂ = {!!}
  -}

  {- Кстати, как можно формулировать такие утверждения?
     Беда в том, что _≡_ неприменимо к операндам разных типов,
     но (как могла бы доказывать прошлая теорема, если бы была верна)
     они на самом деле имеют одинаковый тип
  -}
  {-
  ⟷→≡ : ∀ {n}{f₁ f₂ : Form n}
    → {p₁ : Patch f₁} → {p₂ : Patch f₂}
    → p₁ ⟷ p₂ → p₁ ≡ p₂
  ⟷→≡ p₁⟷p₂ = ?
  -}
  

{- Тут то же самое, что выше, но для двоичных деревьев -}
module TreeWithFunctions (A : Set) where

  open Data-Vec
  open ≡-Prop
  
  data Tree : Set where
    Leaf : (val : A) → Tree
    Branch : (left right : Tree) → Tree
    
  data Shape : Set where
    Take Skip : Shape
    Branch : (left right : Shape) → Shape

  data _∥_ : Shape → Shape → Set where
    ∅∥✴ : (s : Shape) → Skip ∥ s
    ✴∥∅ : (s : Shape) → s ∥ Skip
    Branch-∥ : ∀ {L1 R1 L2 R2 : Shape} → L1 ∥ L2 → R1 ∥ R2 
      → Branch L1 R1 ∥ Branch L2 R2
      
  data Patch : Shape → Set where
    I : Patch Skip
    ⟨_⇒_⟩ : (from to : Tree) → Patch Take
    ⟨_∧_⟩ : ∀ {sl sr : Shape} → (left : Patch sl) (right : Patch sr)
      → Patch (Branch sl sr)
      
  data _⊏_ : ∀ {s : Shape} → Patch s → Tree → Set where
    ⊏-I : (t : Tree) → I ⊏ t
    ⊏-⇒ : (from to : Tree) → ⟨ from ⇒ to ⟩ ⊏ from
    ⊏-∧ : {sl sr : Shape} {pl : Patch sl} {pr : Patch sr} {tl tr : Tree}
      → pl ⊏ tl → pr ⊏ tr → ⟨ pl ∧ pr ⟩ ⊏ Branch tl tr

  ∥-test : Branch Take Skip ∥ Branch Skip Take
  ∥-test = Branch-∥ (✴∥∅ Take) (∅∥✴ Take)

  patch : {s : Shape} → (p : Patch s) → (t : Tree) → p ⊏ t → Tree
  patch I t (⊏-I .t) = t
  patch ⟨ .t ⇒ to ⟩ t (⊏-⇒ .t .to) = to
  patch ⟨ pl ∧ pr ⟩ (Branch tl tr) (⊏-∧ ⊏l ⊏r) = 
    Branch (patch pl tl ⊏l) (patch pr tr ⊏r)

  _^_ : (sl sr : Shape) → sl ∥ sr → Shape
  _^_ .Skip sr (∅∥✴ .sr) = sr
  _^_ sl .Skip (✴∥∅ .sl) = sl
  _^_ (Branch L1 R1) (Branch L2 R2) (Branch-∥ pl pr) = 
    Branch ((L1 ^ L2) pl) ((R1 ^ R2) pr)

  unite : {f₁ f₂ : Shape} → f₁ ∥ f₂ → Shape
  unite {f₁} {f₂} p = (f₁ ^ f₂) p

  _⋀_ : {s₁ s₂ : Shape} (p₁ : Patch s₁) (p₂ : Patch s₂)
    → (s₁∥s₂ : s₁ ∥ s₂) → Patch (unite s₁∥s₂)
  _⋀_ I I (∅∥✴ .Skip) = I
  _⋀_ I I (✴∥∅ .Skip) = I
  _⋀_ I ⟨ from ⇒ to ⟩ (∅∥✴ .Take) = ⟨ from ⇒ to ⟩
  _⋀_ I (⟨_∧_⟩ {sl} {sr} pl pr) (∅∥✴ .(Branch sl sr)) = ⟨ pl ∧ pr ⟩
  _⋀_ ⟨ from ⇒ to ⟩ I (✴∥∅ .Take) = ⟨ from ⇒ to ⟩
  _⋀_ ⟨ from ⇒ to ⟩ ⟨ from₁ ⇒ to₁ ⟩ ()
  _⋀_ ⟨ from ⇒ to ⟩ ⟨ p₂ ∧ p₃ ⟩ ()
  _⋀_ (⟨_∧_⟩ {sl} {sr} pl pr) I (✴∥∅ .(Branch sl sr)) = ⟨ pl ∧ pr ⟩
  _⋀_ ⟨ p₁ ∧ p₂ ⟩ ⟨ from ⇒ to ⟩ ()
  _⋀_ ⟨ p₁ ∧ p₂ ⟩ ⟨ p₃ ∧ p₄ ⟩ (Branch-∥ s₁∥s₂ s₃∥s₄) = 
    ⟨ (p₁ ⋀ p₃) s₁∥s₂ ∧ (p₂ ⋀ p₄) s₃∥s₄ ⟩

  patch-lem : ∀ {s₁ s₂ : Shape} 
    → (x : Tree) → (p : s₁ ∥ s₂)
    → (p₁ : Patch s₁) → (p₂ : Patch s₂)
    → p₁ ⊏ x → p₂ ⊏ x
    → ((p₁ ⋀ p₂) p ⊏ x)
  patch-lem x (∅∥✴ .Skip) I I (⊏-I .x) (⊏-I .x) = ⊏-I x
  patch-lem x (✴∥∅ .Skip) I I (⊏-I .x) (⊏-I .x) = ⊏-I x
  patch-lem x (∅∥✴ .Take) I ⟨ .x ⇒ to ⟩ (⊏-I .x) (⊏-⇒ .x .to) = 
    ⊏-⇒ x to
  patch-lem x (∅∥✴ .(Branch sl sr)) I (⟨_∧_⟩ {sl} {sr} p₂ p₃) p₁⊏x p₂⊏x = p₂⊏x
  patch-lem x (✴∥∅ .Take) ⟨ from ⇒ to ⟩ I p₁⊏x p₂⊏x = p₁⊏x
  patch-lem x (✴∥∅ .(Branch sl sr)) (⟨_∧_⟩ {sl} {sr} p₁ p₂) I p₁⊏x p₂⊏x = p₁⊏x
  patch-lem (Leaf val) (Branch-∥ pl pr) ⟨ p₁ ∧ p₂ ⟩ ⟨ p₃ ∧ p₄ ⟩ () p₂⊏x
  patch-lem (Branch tl tr) (Branch-∥ pl pr) ⟨ p₁ ∧ p₂ ⟩ ⟨ p₃ ∧ p₄ ⟩ (⊏-∧ p₁⊏tl p₂⊏tr) (⊏-∧ p₃⊏tl p₄⊏tr) = 
    ⊏-∧ (patch-lem tl pl p₁ p₃ p₁⊏tl p₃⊏tl) 
        (patch-lem tr pr p₂ p₄ p₂⊏tr p₄⊏tr)

  ∥-comm : ∀ {s₁ s₂ : Shape} → s₁ ∥ s₂ → s₂ ∥ s₁
  ∥-comm {.Skip} {s₂} (∅∥✴ .s₂) = ✴∥∅ s₂
  ∥-comm {s₁} (✴∥∅ .s₁) = ∅∥✴ s₁
  ∥-comm (Branch-∥ s₁∥s₂ s₁∥s₃) = 
    Branch-∥ (∥-comm s₁∥s₂) (∥-comm s₁∥s₃)

  lemma-∥-unite : {s₁ s₂ s₃ : Shape} 
    → (s₁∥s₂ : s₁ ∥ s₂) → s₂ ∥ s₃ → s₁ ∥ s₃
    → unite s₁∥s₂ ∥ s₃
  lemma-∥-unite {.Skip} {s₂} (∅∥✴ .s₂) s₂∥s₃ s₁∥s₃ = s₂∥s₃
  lemma-∥-unite {s₁} (✴∥∅ .s₁) s₂∥s₃ s₁∥s₃ = s₁∥s₃
  lemma-∥-unite (Branch-∥ {L1} {R1} {L2} {R2} L1∥L2 R1∥R2) (✴∥∅ .(Branch L2 R2)) s₁∥s₃ = ✴∥∅ (Branch ((L1 ^ L2) L1∥L2) ((R1 ^ R2) R1∥R2))
  lemma-∥-unite (Branch-∥ L1∥L2 R1∥R2) (Branch-∥ s₂∥s₃ s₂∥s₄) (Branch-∥ s₁∥s₃ s₁∥s₄) = Branch-∥ (lemma-∥-unite L1∥L2 s₂∥s₃ s₁∥s₃)
                                                                                         (lemma-∥-unite R1∥R2 s₂∥s₄ s₁∥s₄)

  {- p₁ ⟷ p₂ ─ p₁ операционно эквивалентен p₂ -}
  _⟷_ : ∀ {s₁ s₂ : Shape} 
    → (p₁ : Patch s₁) → (p₂ : Patch s₂) → Set
  p₁ ⟷ p₂ = ∀ (x : Tree) → (p₁⊏x : p₁ ⊏ x) → (p₂⊏x : p₂ ⊏ x) 
    → patch p₁ x p₁⊏x ≡ patch p₂ x p₂⊏x
    
  patch-⊏-indep : {s : Shape} (p : Patch s) (t : Tree)
    → (⊏₁ ⊏₂ : p ⊏ t)
    → patch p t ⊏₁ ≡ patch p t ⊏₂
  patch-⊏-indep I t (⊏-I .t) (⊏-I .t) = refl
  patch-⊏-indep ⟨ .t ⇒ to ⟩ t (⊏-⇒ .t .to) (⊏-⇒ .t .to) = refl
  patch-⊏-indep (⟨_∧_⟩ {sl}{sr} pl pr) .(Branch tl tr) (⊏-∧ {.sl} {.sr} {.pl} {.pr} {tl} {tr} ⊏₁ ⊏₂) (⊏-∧ ⊏₃ ⊏₄) 
    rewrite patch-⊏-indep pl tl ⊏₁ ⊏₃ | patch-⊏-indep pr tr ⊏₂ ⊏₄ = refl
    
  ∥-comm²≡id : {s₁ s₂ : Shape} → (s₁∥s₂ : s₁ ∥ s₂)
    → s₁∥s₂ ≡ ∥-comm (∥-comm s₁∥s₂)
  ∥-comm²≡id {.Skip} {s₂} (∅∥✴ .s₂) = refl
  ∥-comm²≡id {s₁} (✴∥∅ .s₁) = refl
  ∥-comm²≡id (Branch-∥ L1∥L2 R1∥R2) 
    {- почему-то не захотел работать rewrite. Пришлось сделать with -}
    with ∥-comm (∥-comm L1∥L2) | ∥-comm²≡id L1∥L2
       | ∥-comm (∥-comm R1∥R2) | ∥-comm²≡id R1∥R2
  ∥-comm²≡id (Branch-∥ .i1 .i2) | i1 | refl | i2 | refl = refl
    
  -- Неправда
  {-
  unite-lem : {s₁ s₂ : Shape} → (∥₁ ∥₂ : s₁ ∥ s₂) → ∥₁ ≡ ∥₂
  unite-lem {.Skip} {s₂} (∅∥✴ .s₂) (∅∥✴ .s₂) = refl
  unite-lem (∅∥✴ .Skip) (✴∥∅ .Skip) = {!!}
  unite-lem (✴∥∅ .Skip) (∅∥✴ .Skip) = {!!}
  unite-lem {s₁} (✴∥∅ .s₁) (✴∥∅ .s₁) = {!!}
  unite-lem (Branch-∥ ∥₁ ∥₂) (Branch-∥ ∥₃ ∥₄) = {!!}
  -}
  
  -- Не тайпчекается
  {-
  ⋀-∥-indep : {s₁ s₂ : Shape} (p₁ : Patch s₁) (p₂ : Patch s₂)
    → (∥₁ ∥₂ : s₁ ∥ s₂) → 
    (p₁ ⋀ p₂) ∥₁ ≡ (p₁ ⋀ p₂) ∥₂
  ⋀-∥-indep p₁ p₂ ∥₁ ∥₂ = ?
  -}

  ⋀-comm : ∀ {s₁ s₂ : Shape}
    → (s₁∥s₂ : s₁ ∥ s₂)
    → (p₁ : Patch s₁) → (p₂ : Patch s₂)
    → ((p₁ ⋀ p₂) s₁∥s₂) ⟷ ((p₂ ⋀ p₁) (∥-comm s₁∥s₂))
  ⋀-comm (∅∥✴ .Skip) I I t p₁⊏x p₂⊏x = patch-⊏-indep I t p₁⊏x p₂⊏x
  ⋀-comm (✴∥∅ .Skip) I I t p₁⊏x p₂⊏x = patch-⊏-indep I t p₁⊏x p₂⊏x
  ⋀-comm (∅∥✴ .Take) I ⟨ from ⇒ to ⟩ t p₁⊏x p₂⊏x = 
    patch-⊏-indep ⟨ from ⇒ to ⟩ t p₁⊏x p₂⊏x
  ⋀-comm (∅∥✴ .(Branch sl sr)) I (⟨_∧_⟩ {sl} {sr} p₂ p₃) t p₁⊏x p₂⊏x =
    patch-⊏-indep ⟨ p₂ ∧ p₃ ⟩ t p₁⊏x p₂⊏x
  ⋀-comm (✴∥∅ .Take) ⟨ from ⇒ to ⟩ I t p₁⊏x p₂⊏x = 
    patch-⊏-indep ⟨ from ⇒ to ⟩ t p₁⊏x p₂⊏x
  ⋀-comm (✴∥∅ .(Branch sl sr)) (⟨_∧_⟩ {sl} {sr} p₁ p₂) I t p₁⊏x p₂⊏x = 
    patch-⊏-indep ⟨ p₁ ∧ p₂ ⟩ t p₁⊏x p₂⊏x
  ⋀-comm (Branch-∥ L1∥L2 R1∥R2) 
         ⟨ p₁ ∧ p₂ ⟩ 
         ⟨ p₃ ∧ p₄ ⟩ 
         (Branch tl tr) 
         (⊏-∧ p₁∧p₃⊏tl p₂∧p₄⊏tr) (⊏-∧ p₃∧p₁⊏tl p₄∧p₂⊏tr) 
         rewrite ⋀-comm L1∥L2 p₁ p₃ tl p₁∧p₃⊏tl p₃∧p₁⊏tl 
         |       ⋀-comm R1∥R2 p₂ p₄ tr p₂∧p₄⊏tr p₄∧p₂⊏tr = refl

   
  {- Не надо смотреть на размер доказательства. На самом деле, подавляющее большинство
     случаев доказались сами после вбивания в дырку `patch-⊏-indep` и C-c C-a.
     Не доказались сами только два случая в середине, для них пришлось делать
     `∥-comm²≡id` и один в конце, в котором, как и ожидалось, был рекурсивный вызов.
     Вообще, от того, что у утверждения (s₁ ∥ s₂) может быть два структурно неэквивалентных
     доказательства вылазит куча проблем. -}
  ⋀-assoc : ∀ {s₁ s₂ s₃ : Shape} 
    → (s₁∥s₂ : s₁ ∥ s₂) → (s₂∥s₃ : s₂ ∥ s₃) → (s₁∥s₃ : s₁ ∥ s₃)
    → (p₁ : Patch s₁) → (p₂ : Patch s₂) → (p₃ : Patch s₃)
    → (((p₁ ⋀ p₂) s₁∥s₂) ⋀ p₃) (lemma-∥-unite s₁∥s₂ s₂∥s₃ s₁∥s₃) ⟷ 
      (p₁ ⋀ ((p₂ ⋀ p₃) s₂∥s₃)) 
        (∥-comm (lemma-∥-unite s₂∥s₃ (∥-comm s₁∥s₃) (∥-comm s₁∥s₂)))
  ⋀-assoc (∅∥✴ .Skip) (∅∥✴ .Skip) (∅∥✴ .Skip) I I I t [12]3⊏t 1[23]⊏t = patch-⊏-indep I t [12]3⊏t 1[23]⊏t
  ⋀-assoc (∅∥✴ .Skip) (∅∥✴ .Take) (∅∥✴ .Take) I I ⟨ from ⇒ to ⟩ t [12]3⊏t 1[23]⊏t = patch-⊏-indep ⟨ from ⇒ to ⟩ t [12]3⊏t 1[23]⊏t
  ⋀-assoc (∅∥✴ .Skip) (∅∥✴ .(Branch sl sr)) (∅∥✴ .(Branch sl sr)) I I (⟨_∧_⟩ {sl} {sr} p₃ p₄) t [12]3⊏t 1[23]⊏t = patch-⊏-indep ⟨ p₃ ∧ p₄ ⟩ t [12]3⊏t 1[23]⊏t
  ⋀-assoc (∅∥✴ .Skip) (∅∥✴ .Skip) (✴∥∅ .Skip) I I I t [12]3⊏t 1[23]⊏t = patch-⊏-indep I t [12]3⊏t 1[23]⊏t
  ⋀-assoc (∅∥✴ .Skip) (✴∥∅ .Skip) (∅∥✴ .Skip) I I I t [12]3⊏t 1[23]⊏t = patch-⊏-indep I t [12]3⊏t 1[23]⊏t
  ⋀-assoc (∅∥✴ .Take) (✴∥∅ .Take) (∅∥✴ .Skip) I ⟨ from ⇒ to ⟩ I t [12]3⊏t 1[23]⊏t = patch-⊏-indep ⟨ from ⇒ to ⟩ t [12]3⊏t 1[23]⊏t
  ⋀-assoc (∅∥✴ .(Branch sl sr)) (✴∥∅ .(Branch sl sr)) (∅∥✴ .Skip) I (⟨_∧_⟩ {sl} {sr} p₂ p₃) I t [12]3⊏t 1[23]⊏t = patch-⊏-indep ⟨ p₂ ∧ p₃ ⟩ t [12]3⊏t 1[23]⊏t
  ⋀-assoc (∅∥✴ .Skip) (✴∥∅ .Skip) (✴∥∅ .Skip) I I I t [12]3⊏t 1[23]⊏t = patch-⊏-indep I t [12]3⊏t 1[23]⊏t
  ⋀-assoc (∅∥✴ .Take) (✴∥∅ .Take) (✴∥∅ .Skip) I ⟨ from ⇒ to ⟩ I t [12]3⊏t 1[23]⊏t = patch-⊏-indep ⟨ from ⇒ to ⟩ t [12]3⊏t 1[23]⊏t
  ⋀-assoc (∅∥✴ .(Branch sl sr)) (✴∥∅ .(Branch sl sr)) (✴∥∅ .Skip) I (⟨_∧_⟩ {sl} {sr} p₂ p₃) I t [12]3⊏t 1[23]⊏t = patch-⊏-indep ⟨ p₂ ∧ p₃ ⟩ t [12]3⊏t 1[23]⊏t
  ⋀-assoc (∅∥✴ .(Branch L1 R1)) (Branch-∥ {L1} {R1} {L2} {R2} s₂∥s₃ s₂∥s₄) (∅∥✴ .(Branch L2 R2)) I ⟨ p₂ ∧ p₃ ⟩ ⟨ p₄ ∧ p₅ ⟩ t [12]3⊏t 1[23]⊏t = patch-⊏-indep ⟨ (p₂ ⋀ p₄) s₂∥s₃ ∧ (p₃ ⋀ p₅) s₂∥s₄ ⟩ t [12]3⊏t
                                                                                                                                                 1[23]⊏t
  ⋀-assoc (✴∥∅ .Skip) (∅∥✴ .Skip) (∅∥✴ .Skip) I I I t [12]3⊏t 1[23]⊏t = patch-⊏-indep I t [12]3⊏t 1[23]⊏t
  ⋀-assoc (✴∥∅ .Skip) (∅∥✴ .Take) (∅∥✴ .Take) I I ⟨ from ⇒ to ⟩ t [12]3⊏t 1[23]⊏t = patch-⊏-indep ⟨ from ⇒ to ⟩ t [12]3⊏t 1[23]⊏t
  ⋀-assoc (✴∥∅ .Skip) (∅∥✴ .(Branch sl sr)) (∅∥✴ .(Branch sl sr)) I I (⟨_∧_⟩ {sl} {sr} p₃ p₄) t [12]3⊏t 1[23]⊏t = patch-⊏-indep ⟨ p₃ ∧ p₄ ⟩ t [12]3⊏t 1[23]⊏t
  ⋀-assoc (✴∥∅ .Skip) (∅∥✴ .Skip) (✴∥∅ .Skip) I I I t [12]3⊏t 1[23]⊏t = patch-⊏-indep I t [12]3⊏t 1[23]⊏t
  ⋀-assoc (✴∥∅ .Take) (∅∥✴ .Skip) (✴∥∅ .Take) ⟨ from ⇒ to ⟩ I I t [12]3⊏t 1[23]⊏t = patch-⊏-indep ⟨ from ⇒ to ⟩ t [12]3⊏t 1[23]⊏t
  ⋀-assoc (✴∥∅ .(Branch sl sr)) (∅∥✴ .Skip) (✴∥∅ .(Branch sl sr)) (⟨_∧_⟩ {sl} {sr} p₁ p₂) I I t [12]3⊏t 1[23]⊏t = patch-⊏-indep ⟨ p₁ ∧ p₂ ⟩ t [12]3⊏t 1[23]⊏t
  ⋀-assoc (✴∥∅ .(Branch L1 R1)) (∅∥✴ .(Branch L2 R2)) (Branch-∥ {L1} {R1} {L2} {R2} s₁∥s₃ s₁∥s₄) ⟨ p₁ ∧ p₂ ⟩ I ⟨ p₃ ∧ p₄ ⟩ .(Branch tl tr) (⊏-∧ {.((L1 ^ L2) s₁∥s₃)} {.((R1 ^ R2) s₁∥s₄)} {.((p₁ ⋀ p₃) s₁∥s₃)} {.((p₂ ⋀ p₄) s₁∥s₄)} {tl} {tr} [12]3⊏t [12]3⊏t₁) (⊏-∧ 1[23]⊏t 1[23]⊏t₁) 
    with ∥-comm (∥-comm s₁∥s₃) | ∥-comm²≡id s₁∥s₃
       | ∥-comm (∥-comm s₁∥s₄) | ∥-comm²≡id s₁∥s₄
  ⋀-assoc (✴∥∅ .(Branch L1 R1)) (∅∥✴ .(Branch L2 R2)) (Branch-∥ {L1} {R1} {L2} {R2} .i1 .i2) ⟨ p₁ ∧ p₂ ⟩ I ⟨ p₃ ∧ p₄ ⟩ .(Branch tl tr) (⊏-∧ {.((1[23]⊏t₁ ^ L1) L2 i1)} {.((1[23]⊏t₁ ^ R1) R2 i2)} {.((1[23]⊏t₁ ⋀ p₁) p₃ i1)} {.((1[23]⊏t₁ ⋀ p₂) p₄ i2)} {tl} {tr} [12]3⊏t [12]3⊏t₁) (⊏-∧ 1[23]⊏t 1[23]⊏t₁) | i1 | refl | i2 | refl = 
    cong₂ Branch (patch-⊏-indep ((p₁ ⋀ p₃) i1) tl [12]3⊏t 1[23]⊏t) 
                 (patch-⊏-indep ((p₂ ⋀ p₄) i2) tr [12]3⊏t₁ 1[23]⊏t₁)
  ⋀-assoc (✴∥∅ .Skip) (✴∥∅ .Skip) (∅∥✴ .Skip) I I I t [12]3⊏t 1[23]⊏t = patch-⊏-indep I t [12]3⊏t 1[23]⊏t
  ⋀-assoc (✴∥∅ .Skip) (✴∥∅ .Skip) (✴∥∅ .Skip) I I I t [12]3⊏t 1[23]⊏t = patch-⊏-indep I t [12]3⊏t 1[23]⊏t
  ⋀-assoc (✴∥∅ .Take) (✴∥∅ .Skip) (✴∥∅ .Take) ⟨ from ⇒ to ⟩ I I t [12]3⊏t 1[23]⊏t = patch-⊏-indep ⟨ from ⇒ to ⟩ t [12]3⊏t 1[23]⊏t
  ⋀-assoc (✴∥∅ .(Branch sl sr)) (✴∥∅ .Skip) (✴∥∅ .(Branch sl sr)) (⟨_∧_⟩ {sl} {sr} p₁ p₂) I I t [12]3⊏t 1[23]⊏t = patch-⊏-indep ⟨ p₁ ∧ p₂ ⟩ t [12]3⊏t 1[23]⊏t
  ⋀-assoc (Branch-∥ {L1} {R1} {L2} {R2} s₁∥s₂ s₁∥s₃) (✴∥∅ .(Branch L2 R2)) (✴∥∅ .(Branch L1 R1)) ⟨ p₁ ∧ p₂ ⟩ ⟨ p₃ ∧ p₄ ⟩ I t [12]3⊏t 1[23]⊏t 
    with ∥-comm (∥-comm s₁∥s₃) | ∥-comm²≡id s₁∥s₃
       | ∥-comm (∥-comm s₁∥s₂) | ∥-comm²≡id s₁∥s₂
  ⋀-assoc (Branch-∥ {L1} {R1} {L2} {R2} .i2 .i1) (✴∥∅ .(Branch L2 R2)) (✴∥∅ .(Branch L1 R1)) ⟨ p₁ ∧ p₂ ⟩ ⟨ p₃ ∧ p₄ ⟩ I t [12]3⊏t 1[23]⊏t | i1 | refl | i2 | refl = patch-⊏-indep ⟨ (p₁ ⋀ p₃) i2 ∧ (p₂ ⋀ p₄) i1 ⟩ t [12]3⊏t 1[23]⊏t
  ⋀-assoc (Branch-∥ L1∥L2 R1∥R2) (Branch-∥ L2∥L3 R2∥R3) (Branch-∥ L1∥L3 R1∥R3) ⟨ p₁ ∧ p₂ ⟩ ⟨ p₃ ∧ p₄ ⟩ ⟨ p₅ ∧ p₆ ⟩ (Branch tl tr) (⊏-∧ L[12]3⊏t R[12]3⊏t) (⊏-∧ L1[23]⊏t R1[23]⊏t) 
    rewrite ⋀-assoc L1∥L2 L2∥L3 L1∥L3 p₁ p₃ p₅ tl L[12]3⊏t L1[23]⊏t 
          | ⋀-assoc R1∥R2 R2∥R3 R1∥R3 p₂ p₄ p₆ tr R[12]3⊏t R1[23]⊏t
          = refl




