\begin{code}
module TreeToReport where

open import OXIj.BrutalDepTypes

open ≡-Prop

postulate A : Set

data Tree : Set where
  Leaf : (val : A) → Tree
  Branch : (left right : Tree) → Tree

data Form : Set where
  Take : Form
  Skip : Form
  Branch : (left right : Form) → Form

data _∥_ : Form → Form → Set where
  ∅∥✶ : (s : Form) → Skip ∥ s
  ✶∥∅ : (s : Form) → s ∥ Skip
  Branch-∥ : ∀ {L1 R1 L2 R2 : Form} → L1 ∥ L2 → R1 ∥ R2 
    → Branch L1 R1 ∥ Branch L2 R2

data Patch : Form → Set where
  I : Patch Skip
  ⟨_⇒_⟩ : (from to : Tree) → Patch Take
  ⟨_∧_⟩ : ∀ {sl sr : Form} → (left : Patch sl) (right : Patch sr)
    → Patch (Branch sl sr)

data _⊏_ : ∀ {s : Form} → Patch s → Tree → Set where
  ⊏-I : (t : Tree) → I ⊏ t
  ⊏-⇒ : (from to : Tree) → ⟨ from ⇒ to ⟩ ⊏ from
  ⊏-∧ : {sl sr : Form} {pl : Patch sl} {pr : Patch sr} {tl tr : Tree}
    → pl ⊏ tl → pr ⊏ tr → ⟨ pl ∧ pr ⟩ ⊏ Branch tl tr

patch : {s : Form} → (p : Patch s) → (t : Tree) → p ⊏ t → Tree

patch I t (⊏-I .t) = t

patch ⟨ .t ⇒ to ⟩ t (⊏-⇒ .t .to) = to

patch ⟨ pl ∧ pr ⟩ (Branch tl tr) (⊏-∧ l-a r-a) = 
  Branch (patch pl tl l-a) (patch pr tr r-a)

_⟶_ : ∀ {s₁ s₂ : Form}
  → (p₁ : Patch s₁) → (p₂ : Patch s₂) → Set
_⟶_ {n} p₁ p₂ = ∀ {x : Tree}
  → (p₁-x : p₁ ⊏ x) → Σ (p₂ ⊏ x) (λ p₂-x → 
    (patch p₁ x p₁-x ≡ patch p₂ x p₂-x))

_⟷_ : ∀ {f₁ f₂ : Form}
  → (p₁ : Patch f₁) → (p₂ : Patch f₂) → Set
p₁ ⟷ p₂ = (p₁ ⟶ p₂) ∧ (p₂ ⟶ p₁)

_⟷-bad_ : ∀ {s₁ s₂ : Form} 
  → (p₁ : Patch s₁) → (p₂ : Patch s₂) → Set
p₁ ⟷-bad p₂ = ∀ (x : Tree) → (p₁⊏x : p₁ ⊏ x) → (p₂⊏x : p₂ ⊏ x) 
  → patch p₁ x p₁⊏x ≡ patch p₂ x p₂⊏x

⟷-bad-test : ∀ {a b c d} → a ≠ c → ⟨ a ⇒ b ⟩ ⟷-bad ⟨ c ⇒ d ⟩
⟷-bad-test a≠c a (⊏-⇒ .a _) (⊏-⇒ .a _) = ⊥-elim (a≠c refl)

⟷-refl : ∀ {s : Form} (p : Patch s) → p ⟷ p
⟷-refl p = (λ x → x , refl) , (λ x → x , refl)

⟷-sym : ∀ {s₁ s₂} {p₁ : Patch s₁} {p₂ : Patch s₂}
  → (p₁ ⟷ p₂) → (p₂ ⟷ p₁)
⟷-sym (1⟶2 , 2⟶1) = (2⟶1 , 1⟶2)

⟶-trans : {s₁ s₂ s₃ : Form} 
  → {p₁ : Patch s₁}{p₂ : Patch s₂}{p₃ : Patch s₃}
  → (p₁ ⟶ p₂) → (p₂ ⟶ p₃) → (p₁ ⟶ p₃)
⟶-trans {p₁ = p₁}{p₂}{p₃} 1⟶2 2⟶3 {x} p⊏x 
  with patch p₁ x p⊏x | 1⟶2 p⊏x 
... | ._ | p₂⊏x , refl = 2⟶3 p₂⊏x

⟷-trans : {s₁ s₂ s₃ : Form} 
  → {p₁ : Patch s₁}{p₂ : Patch s₂}{p₃ : Patch s₃}
  → (p₁ ⟷ p₂) → (p₂ ⟷ p₃) → (p₁ ⟷ p₃)
⟷-trans (1⟶2 , 2⟶1) (2⟶3 , 3⟶2) = 
  (⟶-trans 1⟶2 2⟶3) , (⟶-trans 3⟶2 2⟶1)

⟶-branch : ∀ {L1 L2 R1 R2 : Form}
  → {l₁ : Patch L1} {l₂ : Patch L2} {r₁ : Patch R1} {r₂ : Patch R2}
  → (l₁ ⟶ l₂) → (r₁ ⟶ r₂) → ⟨ l₁ ∧ r₁ ⟩ ⟶ ⟨ l₂ ∧ r₂ ⟩
⟶-branch {l₁ = l₁}{l₂}{r₁}{r₂} l₁⟶l₂ r₁⟶r₂ (⊏-∧ {tl = tl}{tr} l⊏L r⊏R) 
  with patch l₁ tl l⊏L | l₁⟶l₂ l⊏L 
    | patch r₁ tr r⊏R | r₁⟶r₂ r⊏R
... | ._ | l₂⊏L , refl | ._ | r₂⊏R , refl = 
  ⊏-∧ l₂⊏L r₂⊏R , refl

⟷-branch : ∀ {L1 L2 R1 R2 : Form}
  → {l₁ : Patch L1} {l₂ : Patch L2} {r₁ : Patch R1} {r₂ : Patch R2}
  → (l₁ ⟷ l₂) → (r₁ ⟷ r₂) → ⟨ l₁ ∧ r₁ ⟩ ⟷ ⟨ l₂ ∧ r₂ ⟩
⟷-branch (l₁⟶l₂ , l₂⟶l₁) (r₁⟶r₂ , r₂⟶r₁) = 
  (⟶-branch l₁⟶l₂ r₁⟶r₂) , (⟶-branch l₂⟶l₁ r₂⟶r₁)

_^_ : (sl sr : Form) → sl ∥ sr → Form
_^_ .Skip sr (∅∥✶ .sr) = sr
_^_ sl .Skip (✶∥∅ .sl) = sl
_^_ (Branch L1 R1) (Branch L2 R2) (Branch-∥ pl pr) = 
  Branch ((L1 ^ L2) pl) ((R1 ^ R2) pr)

unite : {f₁ f₂ : Form} → f₁ ∥ f₂ → Form
unite {f₁} {f₂} p = (f₁ ^ f₂) p

_⋀_ : {s₁ s₂ : Form} (p₁ : Patch s₁) (p₂ : Patch s₂)
  → (s₁∥s₂ : s₁ ∥ s₂) → Patch (unite s₁∥s₂)
_⋀_ I I (∅∥✶ .Skip) = I
_⋀_ I I (✶∥∅ .Skip) = I
_⋀_ I ⟨ from ⇒ to ⟩ (∅∥✶ .Take) = ⟨ from ⇒ to ⟩
_⋀_ I (⟨_∧_⟩ {sl} {sr} pl pr) (∅∥✶ .(Branch sl sr)) = ⟨ pl ∧ pr ⟩
_⋀_ ⟨ from ⇒ to ⟩ I (✶∥∅ .Take) = ⟨ from ⇒ to ⟩
_⋀_ (⟨_∧_⟩ {sl} {sr} pl pr) I (✶∥∅ .(Branch sl sr)) = ⟨ pl ∧ pr ⟩
_⋀_ ⟨ p₁ ∧ p₂ ⟩ ⟨ p₃ ∧ p₄ ⟩ (Branch-∥ s₁∥s₂ s₃∥s₄) = 
  ⟨ (p₁ ⋀ p₃) s₁∥s₂ ∧ (p₂ ⋀ p₄) s₃∥s₄ ⟩

∥-sym : ∀ {s₁ s₂ : Form} → s₁ ∥ s₂ → s₂ ∥ s₁
∥-sym {.Skip} {s₂} (∅∥✶ .s₂) = ✶∥∅ s₂
∥-sym {s₁} (✶∥∅ .s₁) = ∅∥✶ s₁
∥-sym (Branch-∥ s₁∥s₂ s₁∥s₃) = 
  Branch-∥ (∥-sym s₁∥s₂) (∥-sym s₁∥s₃)

lemma-∥-unite : {s₁ s₂ s₃ : Form} 
  → (s₁∥s₂ : s₁ ∥ s₂) → s₂ ∥ s₃ → s₁ ∥ s₃
  → unite s₁∥s₂ ∥ s₃
lemma-∥-unite {.Skip} {s₂} (∅∥✶ .s₂) s₂∥s₃ s₁∥s₃ = s₂∥s₃
lemma-∥-unite {s₁} (✶∥∅ .s₁) s₂∥s₃ s₁∥s₃ = s₁∥s₃
lemma-∥-unite (Branch-∥ {L1} {R1} {L2} {R2} L1∥L2 R1∥R2) 
  (✶∥∅ .(Branch L2 R2)) s₁∥s₃ 
    = ✶∥∅ (Branch ((L1 ^ L2) L1∥L2) ((R1 ^ R2) R1∥R2))
lemma-∥-unite (Branch-∥ L1∥L2 R1∥R2) (Branch-∥ s₂∥s₃ s₂∥s₄) 
  (Branch-∥ s₁∥s₃ s₁∥s₄) 
  = Branch-∥ (lemma-∥-unite L1∥L2 s₂∥s₃ s₁∥s₃)
    (lemma-∥-unite R1∥R2 s₂∥s₄ s₁∥s₄)

∥-sym²≡id : {s₁ s₂ : Form} → (s₁∥s₂ : s₁ ∥ s₂)
  → s₁∥s₂ ≡ ∥-sym (∥-sym s₁∥s₂)
∥-sym²≡id {.Skip} {s₂} (∅∥✶ .s₂) = refl
∥-sym²≡id {s₁} (✶∥∅ .s₁) = refl
∥-sym²≡id (Branch-∥ L1∥L2 R1∥R2) 
  with ∥-sym (∥-sym L1∥L2) | ∥-sym²≡id L1∥L2
     | ∥-sym (∥-sym R1∥R2) | ∥-sym²≡id R1∥R2
∥-sym²≡id (Branch-∥ .i1 .i2) | i1 | refl | i2 | refl = refl

⋀-comm : ∀ {s₁ s₂ : Form}
  → (s₁∥s₂ : s₁ ∥ s₂)
  → (p₁ : Patch s₁) → (p₂ : Patch s₂)
  → ((p₁ ⋀ p₂) s₁∥s₂) ⟷ ((p₂ ⋀ p₁) (∥-sym s₁∥s₂))
⋀-comm (∅∥✶ .Skip) I I = ⟷-refl I
⋀-comm (∅∥✶ .Take) I ⟨ from ⇒ to ⟩ = ⟷-refl ⟨ from ⇒ to ⟩
⋀-comm (∅∥✶ ._) I ⟨ p₂ ∧ p₃ ⟩ = ⟷-refl ⟨ p₂ ∧ p₃ ⟩
⋀-comm (✶∥∅ .Skip) I I = ⟷-refl I
⋀-comm (✶∥∅ .Take) ⟨ from ⇒ to ⟩ I = ⟷-refl ⟨ from ⇒ to ⟩
⋀-comm (✶∥∅ ._) ⟨ p₁ ∧ p₂ ⟩ I = ⟷-refl ⟨ p₁ ∧ p₂ ⟩
⋀-comm (Branch-∥ L1∥L2 R1∥R2) ⟨ l₁ ∧ r₁ ⟩ ⟨ l₂ ∧ r₂ ⟩ 
  = ⟷-branch L R
  where
    L = ⋀-comm L1∥L2 l₁ l₂
    R = ⋀-comm R1∥R2 r₁ r₂

⋀-assoc : ∀ {s₁ s₂ s₃ : Form} 
  → (s₁∥s₂ : s₁ ∥ s₂) → (s₂∥s₃ : s₂ ∥ s₃) → (s₁∥s₃ : s₁ ∥ s₃)
  → (p₁ : Patch s₁) → (p₂ : Patch s₂) → (p₃ : Patch s₃)
  → (((p₁ ⋀ p₂) s₁∥s₂) ⋀ p₃) (lemma-∥-unite s₁∥s₂ s₂∥s₃ s₁∥s₃) ⟷ 
    (p₁ ⋀ ((p₂ ⋀ p₃) s₂∥s₃)) 
      (∥-sym (lemma-∥-unite s₂∥s₃ (∥-sym s₁∥s₃) (∥-sym s₁∥s₂)))
⋀-assoc (∅∥✶ .Skip) (∅∥✶ .Skip) (∅∥✶ .Skip) I I I = ⟷-refl I
⋀-assoc (∅∥✶ .Skip) (∅∥✶ .Take) (∅∥✶ .Take) I I ⟨ from ⇒ to ⟩ = 
  ⟷-refl ⟨ from ⇒ to ⟩
⋀-assoc (∅∥✶ .Skip) (∅∥✶ ._) (∅∥✶ ._) I I ⟨ p₃ ∧ p₄ ⟩ = ⟷-refl ⟨ p₃ ∧ p₄ ⟩
⋀-assoc (∅∥✶ .Skip) (∅∥✶ .Skip) (✶∥∅ .Skip) I I I = ⟷-refl I
⋀-assoc (∅∥✶ .Skip) (✶∥∅ .Skip) (∅∥✶ .Skip) I I I = ⟷-refl I
⋀-assoc (∅∥✶ .Take) (✶∥∅ .Take) (∅∥✶ .Skip) I ⟨ from ⇒ to ⟩ I = 
  ⟷-refl ⟨ from ⇒ to ⟩
⋀-assoc (∅∥✶ ._) (✶∥∅ ._) (∅∥✶ .Skip) I ⟨ p₂ ∧ p₃ ⟩ I = ⟷-refl ⟨ p₂ ∧ p₃ ⟩
⋀-assoc (∅∥✶ .Skip) (✶∥∅ .Skip) (✶∥∅ .Skip) I I I = ⟷-refl I
⋀-assoc (∅∥✶ .Take) (✶∥∅ .Take) (✶∥∅ .Skip) I ⟨ from ⇒ to ⟩ I = 
  ⟷-refl ⟨ from ⇒ to ⟩
⋀-assoc (∅∥✶ ._) (✶∥∅ ._) (✶∥∅ .Skip) I ⟨ p₂ ∧ p₃ ⟩ I = ⟷-refl ⟨ p₂ ∧ p₃ ⟩
⋀-assoc (∅∥✶ ._) (Branch-∥ s₂∥s₃ s₂∥s₄) (∅∥✶ ._) I ⟨ p₂ ∧ p₃ ⟩ ⟨ p₄ ∧ p₅ ⟩ =
  ⟷-refl ⟨ (p₂ ⋀ p₄) s₂∥s₃ ∧ (p₃ ⋀ p₅) s₂∥s₄ ⟩
⋀-assoc (✶∥∅ .Skip) (∅∥✶ .Skip) (∅∥✶ .Skip) I I I = ⟷-refl I
⋀-assoc (✶∥∅ .Skip) (∅∥✶ .Take) (∅∥✶ .Take) I I ⟨ from ⇒ to ⟩ = 
  ⟷-refl ⟨ from ⇒ to ⟩
⋀-assoc (✶∥∅ .Skip) (∅∥✶ ._) (∅∥✶ ._) I I ⟨ p₃ ∧ p₄ ⟩ = ⟷-refl ⟨ p₃ ∧ p₄ ⟩
⋀-assoc (✶∥∅ .Skip) (∅∥✶ .Skip) (✶∥∅ .Skip) I I I = ⟷-refl I
⋀-assoc (✶∥∅ .Take) (∅∥✶ .Skip) (✶∥∅ .Take) ⟨ from ⇒ to ⟩ I I = 
  ⟷-refl ⟨ from ⇒ to ⟩
⋀-assoc (✶∥∅ ._) (∅∥✶ .Skip) (✶∥∅ ._) ⟨ p₁ ∧ p₂ ⟩ I I = ⟷-refl ⟨ p₁ ∧ p₂ ⟩
⋀-assoc (✶∥∅ ._) (∅∥✶ ._) (Branch-∥ s₁∥s₃ s₂∥s₄) ⟨ p₁ ∧ p₂ ⟩ I ⟨ p₃ ∧ p₄ ⟩ 
  with ∥-sym (∥-sym s₁∥s₃) | ∥-sym²≡id s₁∥s₃ 
    | ∥-sym (∥-sym s₂∥s₄) | ∥-sym²≡id s₂∥s₄
... | .s₁∥s₃ | refl | .s₂∥s₄ | refl = 
  ⟷-refl ⟨ (p₁ ⋀ p₃) s₁∥s₃ ∧ (p₂ ⋀ p₄) s₂∥s₄ ⟩
⋀-assoc (✶∥∅ .Skip) (✶∥∅ .Skip) (∅∥✶ .Skip) I I I = ⟷-refl I
⋀-assoc (✶∥∅ .Skip) (✶∥∅ .Skip) (✶∥∅ .Skip) I I I = ⟷-refl I
⋀-assoc (✶∥∅ .Take) (✶∥∅ .Skip) (✶∥∅ .Take) ⟨ from ⇒ to ⟩ I I = 
  ⟷-refl ⟨ from ⇒ to ⟩
⋀-assoc (✶∥∅ ._) (✶∥∅ .Skip) (✶∥∅ ._) ⟨ p₁ ∧ p₂ ⟩ I I = ⟷-refl ⟨ p₁ ∧ p₂ ⟩
⋀-assoc (Branch-∥ s₁∥s₃ s₂∥s₄) (✶∥∅ ._) (✶∥∅ ._) ⟨ p₁ ∧ p₂ ⟩ ⟨ p₃ ∧ p₄ ⟩ I
  with ∥-sym (∥-sym s₁∥s₃) | ∥-sym²≡id s₁∥s₃ 
    | ∥-sym (∥-sym s₂∥s₄) | ∥-sym²≡id s₂∥s₄
... | .s₁∥s₃ | refl | .s₂∥s₄ | refl = 
  ⟷-refl ⟨ (p₁ ⋀ p₃) s₁∥s₃ ∧ (p₂ ⋀ p₄) s₂∥s₄ ⟩
⋀-assoc (Branch-∥ L1∥L2 R1∥R2) (Branch-∥ L2∥L3 R2∥R3) (Branch-∥ L1∥L3 R1∥R3) 
  ⟨ p₁ ∧ p₂ ⟩ ⟨ p₃ ∧ p₄ ⟩ ⟨ p₅ ∧ p₆ ⟩ = 
    ⟷-branch 
      (⋀-assoc L1∥L2 L2∥L3 L1∥L3 p₁ p₃ p₅) 
      (⋀-assoc R1∥R2 R2∥R3 R1∥R3 p₂ p₄ p₆)

data _⋙?_ : {s₁ s₂ : Form} (p₁ : Patch s₁) (p₂ : Patch s₂) → Set where
  ✶⋙?I : ∀ {s : Form} (p : Patch s) → p ⋙? I
  Here-⋙? : ∀ (t₁ t₂ t₃ : Tree) → ⟨ t₁ ⇒ t₂ ⟩ ⋙? ⟨ t₂ ⇒ t₃ ⟩
  Branch-⋙? : ∀ {s₁ s₂ s₃ s₄} 
    → {p₁ : Patch s₁} {p₂ : Patch s₂} {p₃ : Patch s₃} {p₄ : Patch s₄}
    → (L : p₁ ⋙? p₂) → (R : p₃ ⋙? p₄) → ⟨ p₁ ∧ p₃ ⟩ ⋙? ⟨ p₂ ∧ p₄ ⟩

⋙?-uniq : ∀ {s₁ s₂ : Form} {p₁ : Patch s₁} {p₂ : Patch s₂}
  → (?₁ ?₂ : p₁ ⋙? p₂) → ?₁ ≡ ?₂
⋙?-uniq (✶⋙?I p₁) (✶⋙?I .p₁) = refl
⋙?-uniq (Here-⋙? t₁ t₂ t₃) (Here-⋙? .t₁ .t₂ .t₃) = refl
⋙?-uniq (Branch-⋙? ?₁ ?₂) (Branch-⋙? ?₃ ?₄) 
  rewrite ⋙?-uniq ?₁ ?₃ | ⋙?-uniq ?₂ ?₄ = refl

⋙ : {s₁ s₂ : Form} {p₁ : Patch s₁} {p₂ : Patch s₂}
  → p₁ ⋙? p₂ → Patch s₁
⋙ (✶⋙?I p) = p
⋙ (Here-⋙? t₁ t₂ t₃) = ⟨ t₁ ⇒ t₃ ⟩
⋙ (Branch-⋙? p₁⋙?p₂ p₃⋙?p₄) = ⟨ ⋙ p₁⋙?p₂ ∧ ⋙ p₃⋙?p₄ ⟩

⋙-preserves : ∀ {s₁ s₂ : Form} {p₁ : Patch s₁} {p₂ : Patch s₂}
  → (?₁ ?₂ : p₁ ⋙? p₂) → ⋙ ?₁ ⟷ ⋙ ?₂
⋙-preserves (✶⋙?I p₁) (✶⋙?I .p₁) = ⟷-refl p₁
⋙-preserves (Here-⋙? t₁ t₂ t₃) (Here-⋙? .t₁ .t₂ .t₃) = 
  ⟷-refl ⟨ t₁ ⇒ t₃ ⟩
⋙-preserves (Branch-⋙? ?₁ ?₂) (Branch-⋙? ?₃ ?₄) = 
  ⟷-branch (⋙-preserves ?₁ ?₃) (⋙-preserves ?₂ ?₄)

⋙-assoc : ∀ {s₁ s₂ s₃ : Form} {p₁ : Patch s₁} {p₂ : Patch s₂} {p₃ : Patch s₃}
  → (1⋙?2 : p₁ ⋙? p₂)
  → ([1⋙2]⋙?3 : (⋙ 1⋙?2) ⋙? p₃)
  → (2⋙?3 : p₂ ⋙? p₃)
  → (1⋙?[2⋙3] : p₁ ⋙? (⋙ 2⋙?3))
  → (⋙ [1⋙2]⋙?3) ⟷ (⋙ 1⋙?[2⋙3])
⋙-assoc (✶⋙?I p₁) (✶⋙?I .p₁) (✶⋙?I .I) (✶⋙?I .p₁) = ⟷-refl p₁
⋙-assoc (Here-⋙? t₁ t₂ t₃) (✶⋙?I .(⟨ t₁ ⇒ t₃ ⟩)) (✶⋙?I .(⟨ t₂ ⇒ t₃ ⟩)) 
  (Here-⋙? .t₁ .t₂ .t₃) = ⟷-refl ⟨ t₁ ⇒ t₃ ⟩
⋙-assoc (Here-⋙? t₁ t₂ t₃) (Here-⋙? .t₁ .t₃ t₄) (Here-⋙? .t₂ .t₃ .t₄) 
  (Here-⋙? .t₁ .t₂ .t₄) = ⟷-refl ⟨ t₁ ⇒ t₄ ⟩
⋙-assoc 
  (Branch-⋙? 1⋙?2 3⋙?4) 
  (✶⋙?I .(⟨ ⋙ 1⋙?2 ∧ ⋙ 3⋙?4 ⟩)) 
  (✶⋙?I ._) 
  (Branch-⋙? 1⋙?[2⋙0] 3⋙?[4⋙0]) 
  = ⟷-branch (⋙-preserves 1⋙?2 1⋙?[2⋙0]) 
    (⋙-preserves 3⋙?4 3⋙?[4⋙0])
⋙-assoc 
  (Branch-⋙? 1⋙?2 3⋙?4) 
  (Branch-⋙? [1⋙2]⋙?5 [3⋙4]⋙?6) 
  (Branch-⋙? 2⋙?5 4⋙?6) 
  (Branch-⋙? 1⋙?[2⋙5] 3⋙?[4⋙6]) 
  = ⟷-branch 
    (⋙-assoc 1⋙?2 [1⋙2]⋙?5 2⋙?5 1⋙?[2⋙5]) 
    (⋙-assoc 3⋙?4 [3⋙4]⋙?6 4⋙?6 3⋙?[4⋙6])

module ⋙-try1 where
  data _⋙??_ : {s₁ s₂ : Form} (p₁ : Patch s₁) (p₂ : Patch s₂) → Set where
    ✶⋙?I : ∀ {s : Form} (p : Patch s) → p ⋙?? I
    Here-⋙? : ∀ (t₁ t₂ t₃ : Tree) → ⟨ t₁ ⇒ t₂ ⟩ ⋙?? ⟨ t₂ ⇒ t₃ ⟩
    There-⋙? : ∀ {s₁ s₂ : Form} {t₁ t₂ : Tree} {p₁ : Patch s₁} {p₂ : Patch s₂}
      → (t : Tree) → p₁ ⊏ t₁ → p₂ ⊏ t₂ 
      → ⟨ t ⇒ Branch t₁ t₂ ⟩ ⋙?? ⟨ p₁ ∧ p₂ ⟩
    Branch-⋙? : ∀ {s₁ s₂ s₃ s₄} 
      → {p₁ : Patch s₁} {p₂ : Patch s₂} {p₃ : Patch s₃} {p₄ : Patch s₄}
      → (L : p₁ ⋙?? p₂) → (R : p₃ ⋙?? p₄) → ⟨ p₁ ∧ p₃ ⟩ ⋙?? ⟨ p₂ ∧ p₄ ⟩

\end{code}
