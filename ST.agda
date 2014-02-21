{-
  Author: Jan Malakhovski
  Date: Nov 17, 2013
-}

-- An excercise on de Bruijn Church-style Simply Typed Lambda Calculus
-- and its properties.
module ST where

open import OXIj.BrutalDepTypes
open Data-List
open Data-Any
open ≡-Prop

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

module GeneralizedCurchRosser where
  -- Confluent relation
  Confluent : ∀ {A} (R : A → A → Set) → Set
  Confluent {A} R = ∀ {a b c} → R a b → R a c → Σ A λ d → R b d ∧ R c d

  {- Given a, b, c, R a b, and R a c

        R
      a - b
     R|
      c

     Gives d, R b d, and R c d

         b
         ⋮ R
     c ⋯ d
       R

     to complete the square

     a - b
     |   ⋮
     c ⋯ d
  -}

  module Proof where
    -- column building
    yCR : ∀ {A} {R : A → A → Set}
        → Confluent R → ∀ {a b c}
        → R a b → (R ✴) a c
        → Σ A λ d → (R ✴) b d ∧ R c d
    yCR cr {b = b} Rab ε = b , ε , Rab
    yCR cr Rab (Raa₂ ∷✴ R✴a₂c) with cr Rab Raa₂
    ... | _ , Rbb₂ , Ra₂b₂ with yCR cr Ra₂b₂ R✴a₂c
    ... | d , R✴b₂d , Rcd = d , ((Rbb₂ ∷✴ R✴b₂d) , Rcd)
{-    yCR cr Rab (Raa₂ ∷✴ R✴a₂c) with cr Rab Raa₂
    ... | _ , Rbb₂ , Ra₂b₂ with yCR cr Ra₂b₂ R✴a₂c
    ... | d , R✴b₂d , Rcd = d , ((Rbb₂ ∷✴ R✴b₂d) , Rcd)
-}
    
    -- concatenating columns into a table
    xCR : ∀ {A} {R : A → A → Set} → Confluent R → Confluent (R ✴)
    xCR cr {b = b} x ε = b , ε , x
    xCR cr R✴ab (Raa₁ ∷✴ R✴a₁c) with yCR cr Raa₁ R✴ab
    ... | b₁ , R✴a₁b₁ , Rbb₁ with xCR cr R✴a₁b₁ R✴a₁c
    ... | d , R✴b₁d , R✴cd = d , Rbb₁ ∷✴ R✴b₁d , R✴cd


  -- Confluent relations have confluent closures
  CR : ∀ {A} {R : A → A → Set} → Confluent R → Confluent (R ✴)
  CR = Proof.xCR

open GeneralizedCurchRosser public

module SimptyTypedLambdaCalculusAtomicallyTypedWith (T : Set) where
  -- Simple types
  infixr 5 _→'_
  data Type : Set where
    ✶_   : T → Type
    _→'_ : Type → Type → Type

  -- Context
  Ctx : Set
  Ctx = List Type

  open Membership {A = Type} _≡_

  -- Simply typed λ-term
  data Term (Γ : Ctx) : Type → Set where
    ⋆_  : ∀ {A} → A ∈ Γ → Term Γ A
    Λ   : ∀ {A B} → Term (A ∷ Γ) B → Term Γ (A →' B)
    _∙_ : ∀ {A B} → Term Γ (A →' B) → Term Γ A → Term Γ B

  -- Context (free variables) manipulations:

  -- Add free variable
  _↓w⋯_ : ∀ {Γ Δ} γ → Γ ⊆ Δ → Γ ⊆ (γ ∷ Δ)
  _↓w⋯_ γ f n = there (f n)

  -- Remove free variable
  _↑w⋯_ : ∀ {Γ Δ} γ → (γ ∷ Γ) ⊆ Δ → Γ ⊆ Δ
  _↑w⋯_ γ f n = f (there n)

  -- Skip free variable
  _∷w⋯_ : ∀ {Γ Δ} γ → Γ ⊆ Δ → (γ ∷ Γ) ⊆ (γ ∷ Δ)
  _∷w⋯_ γ f (here refl) = here refl
  _∷w⋯_ γ f (there n) = there (f n)

  -- Skip a bunch of free variables
  _w⋯_ : ∀ {Γ Δ} γs → Γ ⊆ Δ → (γs ++ Γ) ⊆ (γs ++ Δ)
  []     w⋯ f = f
  γ ∷ γs w⋯ f = γ ∷w⋯ γs w⋯ f

  -- Example:
  -- Adding a new free variable σ after free variables γs:
  --   γs w⋯ σ ∷w⋯ id
  -- .

  -- Weakening: apply context manipulation to a λ-term
  wk : ∀ {Γ Δ τ} → Term Γ τ → (Γ ⊆ Δ) → Term Δ τ
  wk (⋆ x) f = ⋆ (f x)
  wk (Λ {A} M) f = Λ (wk M (A ∷w⋯ f))
  wk (M ∙ N) f = wk M f ∙ wk N f

  -- Parallel substitution
  -- Change a term with context Γ to a term with
  -- context Δ by
  data Sub : (Γ Δ : Ctx) → Set where
    [[]]     : Sub [] []
    [_↦_]∷⋯_ : ∀ {Γ Δ} γ → Term Δ γ → Sub Γ Δ → Sub (γ ∷ Γ) Δ -- substituting
    _∷⋯_     : ∀ {Γ Δ} γ → Sub Γ Δ  → Sub (γ ∷ Γ) (γ ∷ Δ)     -- or skipping
  -- free variables.
  -- Sub is a function with finite domain, represented by a list of respective
  -- codomain elements.

  -- Skip a bunch of variables
  _⋯_      : ∀ {Γ Δ} γs → Sub Γ Δ → Sub (γs ++ Γ) (γs ++ Δ)
  [] ⋯ ss = ss
  (γ ∷ γs) ⋯ ss = γ ∷⋯ (γs ⋯ ss)

  -- Identity substitution
  [id] : ∀ {Γ} → Sub Γ Γ
  [id] {[]} = [[]]
  [id] {γ ∷ Γ} = γ ∷⋯ [id]

  -- Syntax sugar
  [_↦_] : ∀ {Γ} γ → Term Γ γ → Sub (γ ∷ Γ) Γ
  [ γ ↦ M ] = [ γ ↦ M ]∷⋯ [id]

  infixr 4 _∷⋯_ _⋯_
  infixr 4 _∷w⋯_ _↓w⋯_ _w⋯_

  -- Extract a term from a substitution by its number in a context
  _!_ : ∀ {Γ Δ τ} → Sub Γ Δ → τ ∈ Γ → Term Δ τ
  [[]]             ! ()
  ([ γ ↦ x ]∷⋯ ss) ! here refl = x
  ([ γ ↦ x ]∷⋯ ss) ! there n   = ss ! n
  (γ        ∷⋯ ss) ! here refl = ⋆ here refl
  (γ        ∷⋯ ss) ! there n   = wk (ss ! n) (γ ↓w⋯ id)

  -- Apply substitution to a term
  sub : ∀ {Γ Δ τ} → Term Γ τ → Sub Γ Δ → Term Δ τ
  sub (⋆ x) ss = ss ! x
  sub (Λ {A} M) ss = Λ (sub M (A ∷⋯ ss))
  sub (M ∙ N) ss = sub M ss ∙ sub N ss


  id!x : ∀ {Γ τ} (x : τ ∈ Γ) → [id] ! x ≡ ⋆ x
  id!x (here refl) = refl
  id!x {a ∷ as} {τ} (there x) with [id] ! x | id!x x
  id!x {a ∷ as} {τ} (there x) | .(⋆ x) | refl = refl

  w⋯-pre : ∀ {Γ Δ E τ}
       → (A : Ctx)
       → (f : Γ ⊆ Δ) → (g : Δ ⊆ E)
       → (x : τ ∈ (A ++ Γ))
       → (A w⋯ g) ((A w⋯ f) x) ≡ (A w⋯ (g ∘ f)) x
  w⋯-pre [] f g x = refl
  w⋯-pre (x ∷ A) f g (here refl) = refl
  w⋯-pre (x ∷ A) f g (there x₁) rewrite w⋯-pre A f g x₁ = refl

  w⋯-pre2 : ∀ {Γ Δ E τ}
          → (A B : Ctx)
          → (f : Γ ⊆ Δ) → (g : Δ ⊆ E)
          → (x : τ ∈ (B ++ A ++ Γ))
          → (B w⋯ ((A w⋯ g) ∘ (A w⋯ f))) x ≡ (B w⋯ (A w⋯ (g ∘ f))) x
  w⋯-pre2 A [] f g x = w⋯-pre A f g x
  w⋯-pre2 A (x ∷ B) f g (here refl) = refl
  w⋯-pre2 A (x ∷ B) f g (there x₁) rewrite w⋯-pre2 A B f g x₁ = refl

  qqq : ∀ {Γ Δ E τ}
      → (A B : Ctx)
      → (f : Γ ⊆ Δ) (g : Δ ⊆ E)
      → (t : Term (B ++ A ++ Γ) τ)
      → wk t (B w⋯ ((A w⋯ g) ∘ (A w⋯ f))) ≡ wk t (B w⋯ A w⋯ (g ∘ f))
  qqq A B f g (⋆ x) rewrite w⋯-pre2 A B f g x = refl
  qqq A B f g (Λ {γ} t) rewrite qqq A (γ ∷ B) f g t = refl
  qqq A B f g (t ∙ t₁) = cong₂ _∙_ (qqq A B f g t) (qqq A B f g t₁)

  wk-trans : ∀ {Γ Δ E τ} (t : Term Γ τ) (f : Γ ⊆ Δ) (g : Δ ⊆ E)
    → wk (wk t f) g ≡ wk t (⊆-trans f g)
  wk-trans (⋆ x) f g = refl
  wk-trans (Λ {γ} t) f g with 
    wk (wk t (γ ∷w⋯ f)) (γ ∷w⋯ g) |
    wk-trans t (γ ∷w⋯ f) (γ ∷w⋯ g)
  wk-trans (Λ {A} t) f g | .(wk t ((A ∷w⋯ g) ∘ (A ∷w⋯ f))) | refl = cong Λ (qqq (A ∷ []) [] f g t)
  wk-trans (t ∙ t₁) f g = cong₂ _∙_ (wk-trans t f g) (wk-trans t₁ f g)

{-  t : ∀ {Γ γ}
    → (A : Ctx) → (x : Type)
    → γ ∈ (A ++ Γ)
    → γ ∈ (A ++ x ∷ Γ)
  t p = {!!}

  wkk : ∀ {Γ γ x}
      → (A : Ctx)
      → ∀ {Δ} → (f : Γ ⊆ Δ)
      → (s : Term (A ++ Γ) γ)
      → wk (wk s (A w⋯ f)) (A w⋯ there)
      ≡ wk (wk s (A w⋯ there)) (A w⋯ x ∷w⋯ f)    
  wkk = {!!}
{-  wkk [] f (⋆ here refl) = refl
  wkk [] f (⋆ there x₁) = refl
  wkk (x₁ ∷ A) f (⋆ here refl) = refl
  wkk {Γ}{γ}{x} (x₁ ∷ A) f (⋆ there x₂) rewrite w⋯-pre A f there x₂ 
    = {!w⋯-pre A f there!}
  wkk A f (Λ {γ} s) = cong Λ (wkk (γ ∷ A) f s)
  wkk A f (s ∙ s₁) = cong₂ _∙_ (wkk A f s) (wkk A f s₁)
-}

  wk-wk : ∀ {Γ Δ γ τ}
        → (A : Ctx) → (f : Γ ⊆ Δ) → (s : Term Γ γ)
        → ∀ x → (x₁ : τ ∈ (A ++ γ ∷ Γ))
        → wk ((A ⋯ [ γ ↦ wk s f ]) ! (A w⋯ γ ∷w⋯ f) x₁) there
        ≡ wk (wk ((A ⋯ [ γ ↦ s ]) ! x₁) there) (x ∷w⋯ A w⋯ f)
  wk-wk [] f (⋆ here refl) x₁ (here refl) = refl
  wk-wk [] f (⋆ there x) x₁ (here refl) = refl
  wk-wk [] f (Λ {γ} s) x (here refl) = cong Λ (wkk (γ ∷ []) f s)
  wk-wk [] f (s ∙ s₁) x (here refl) = 
    cong₂ _∙_ (wkk [] f s) (wkk [] f s₁)
  wk-wk [] f s x (there x₁) rewrite id!x x₁ | id!x (f x₁) = refl
  wk-wk (x ∷ A) f (⋆ here refl) x₂ (here refl) = refl
  wk-wk (x ∷ A) f (⋆ here pa) x₂ (there x₃) = {!!}
  wk-wk (x ∷ A) f (⋆ there x₁) x₂ (here pa) = {!!}
  wk-wk (x ∷ A) f (⋆ there x₁) x₂ (there x₃) = {!!}
  wk-wk (x ∷ A) f (Λ s) x₁ x₂ = {!!}
  wk-wk (x ∷ A) f (s ∙ s₁) x₁ x₂ = {!!}

  www : ∀ {Γ Δ γ τ}
      → (A : Ctx)
      → (f : Γ ⊆ Δ) -- (g : Δ ⊆ E)
      → (s : Term Γ γ)
      → (x : τ ∈ (A ++ γ ∷ Γ))
      → wk ((A ⋯ [ γ ↦ wk s f ]) ! (A w⋯ γ ∷w⋯ f) x) (λ {x₁} → there)
      ≡ wk ((A ⋯ [ γ ↦ s ]) ! x) (λ {x₂} x₁ → there ((A w⋯ f) x₁))
  www A f s x = {!!}

-}
  lemma-wk-g : ∀ {Γ Δ γ τ}
             → (A : Ctx) → (f : Γ ⊆ Δ)
             → (M : Term (A ++ γ ∷ Γ) τ) → (s : Term Γ γ)
             → sub (wk M (A w⋯ γ ∷w⋯ f)) (A ⋯ [ γ ↦ wk s f ])
             ≡ wk (sub M (A ⋯ [ γ ↦ s ])) (A w⋯ f)
  lemma-wk-g (a ∷ as) f (⋆ here refl) s = refl
  lemma-wk-g {Γ}{Δ}{γ}{τ} (a ∷ as) f (⋆ there x) s rewrite
    wk-trans ((as ⋯ [ γ ↦ s ]) ! x) (λ {x₁} → there) (a ∷w⋯ as w⋯ f) 
      = {!!}
--    wk-wk as f s a x
  lemma-wk-g [] f (⋆ here refl) s = refl
  lemma-wk-g [] f (⋆ there x) s rewrite id!x x | id!x (f x) = refl
  lemma-wk-g A f (Λ {γ} M) s = cong Λ 
    (lemma-wk-g (γ ∷ A) f M s)
  lemma-wk-g A f (M ∙ M₁) s = cong₂ _∙_ 
    (lemma-wk-g A f M s) 
    (lemma-wk-g A f M₁ s)

  -- Weakening commutes with substitution
  -- This is specific for the current term representation.
  lemma-wk : ∀ {Γ Δ τ γ}
           → (f : Γ ⊆ Δ)
           → (M : Term (γ ∷ Γ) τ) (s : Term Γ γ)
           → sub (wk M (γ ∷w⋯ f)) [ γ ↦ wk s f ]
           ≡ wk (sub M [ γ ↦ s ]) f
  lemma-wk = lemma-wk-g []

  -- The Substitution Lemma: substitution commutes with itself
  -- This is general.
  lemma-sub : ∀ {Γ Δ σ τ}
              → (M : Term (σ ∷ Γ) τ) (N : Term Γ σ)
              → (ss : Sub Γ Δ)
              → sub (sub M (σ ∷⋯ ss)) [ σ ↦ sub N ss ]
              ≡ sub (sub M [ σ ↦ N ]) ss
  lemma-sub = {!!}


  -- β-reduction
  data _→β_ {Γ} : ∀ {τ} → Term Γ τ → Term Γ τ → Set where
    reduce : ∀ {τ γ} {M : Term (γ ∷ Γ) τ} {N : Term Γ γ} → ((Λ M) ∙ N) →β (sub M [ γ ↦ N ])
    under  : ∀ {τ γ} {M N : Term (γ ∷ Γ) τ} → M →β N → (Λ M) →β (Λ N)
    left   : ∀ {τ σ} {M N : Term Γ (σ →' τ)} {L : Term Γ σ} → M →β N → (M ∙ L) →β (N ∙ L)
    right  : ∀ {τ σ} {M N : Term Γ σ} {L : Term Γ (σ →' τ)} → M →β N → (L ∙ M) →β (L ∙ N)

  -- β-reduction sequence
  _→β✴_ : ∀ {Γ τ} → Term Γ τ → Term Γ τ → Set
  _→β✴_ = _→β_ ✴

  -- We want to prove that →β✴ is confluent, the problem is →β is not confluent
  -- (no free GeneralizedCR proof).
  -- That's why we define

  -- Parallel β-reduction
  data _⇉β_ {Γ} : ∀ {τ} → Term Γ τ → Term Γ τ → Set where
    parsame   : ∀ {τ} → {M : Term Γ τ} → M ⇉β M
    parreduce : ∀ {τ γ} {M M' : Term (γ ∷ Γ) τ} {N N' : Term Γ γ} → M ⇉β M' → N ⇉β N' → ((Λ M) ∙ N) ⇉β (sub M' [ γ ↦ N' ])
    parunder  : ∀ {τ γ} {M N : Term (γ ∷ Γ) τ} → M ⇉β N → (Λ M) ⇉β (Λ N)
    parapp    : ∀ {τ σ} {M M' : Term Γ (σ →' τ)} {N N' : Term Γ σ} → M ⇉β M' → N ⇉β N' → (M ∙ N) ⇉β (M' ∙ N')

  -- Parallel β-reduction sequence
  _⇉β✴_ : ∀ {Γ τ} → Term Γ τ → Term Γ τ → Set
  _⇉β✴_ = _⇉β_ ✴

  -- with ⇉β being confluent (GeneralizedCR!), and ⇉β✴ being the same thing as →β✴.
  -- The rest of the module proves this.

  module TechnicalReductionLemmas where
    -- Useful transformations:
    →β-≡ : ∀ {Γ τ} → {M N M' N' : Term Γ τ} → M ≡ M' → N ≡ N' → M →β N → M' →β N'
    →β-≡ refl refl red = red

    ⇉β-≡ : ∀ {Γ τ} → {M N M' N' : Term Γ τ} → M ≡ M' → N ≡ N' → M ⇉β N → M' ⇉β N'
    ⇉β-≡ refl refl red = red

    -- ?

    {- TechnicalReductionLemmas end -}

  →β✴-∙ : ∀ {Γ τ γ}
     → {N N₁ : Term Γ γ}
     → {M M₁ : Term Γ (γ →' τ)}
     → (N →β✴ N₁) → (M →β✴ M₁)
     → (M ∙ N) →β✴ (M₁ ∙ N₁)
  →β✴-∙ {N₁ = N₁} {M = M} p1 p2 = 
    map✴ (_∙_ M) right p1 ++✴ map✴ (λ z → z ∙ N₁) left p2

  →β✴-Λ : ∀ {Γ τ γ}
        → {M M' : Term (γ ∷ Γ) τ} → (M →β✴ M')
        → (Λ M) →β✴ (Λ M')
  →β✴-Λ p = map✴ Λ under p

  →β✴-sub-R : ∀ {Γ τ γ}
           → (M : Term (γ ∷ Γ) τ)
           → {N N' : Term Γ γ} → N →β✴ N'
           → sub M [ γ ↦ N ] →β✴ sub M [ γ ↦ N' ]
  →β✴-sub-R _ ε = ε
  →β✴-sub-R (⋆ here refl) p = p
  →β✴-sub-R (⋆ there x) _ = ε
  →β✴-sub-R (Λ M) p = →β✴-sub-R (Λ M) p
  →β✴-sub-R (M ∙ M₁) (x ∷✴ N→β✴N') = →β✴-∙
    (→β✴-sub-R M₁ (x ∷✴ N→β✴N')) (→β✴-sub-R M (x ∷✴ N→β✴N'))

  →β-sub-L-g : ∀ {Γ τ γ}
             → (A : Ctx)
             → {M M' : Term (A ++ γ ∷ Γ) τ} → (M →β M')
             → (N : Term Γ γ)
             → sub M (A ⋯ [ γ ↦ N ]) →β✴ sub M' (A ⋯ [ γ ↦ N ])
  →β-sub-L-g {Γ}{τ}{γ} A {Λ {B} M ∙ K}{.(sub M [ B ↦ K ])} reduce N 
    with sub (sub M [ B ↦ K ]) (A ⋯ [ γ ↦ N ]) | 
         lemma-sub M K (A ⋯ [ γ ↦ N ]) 
  →β-sub-L-g {Γ} {τ} {γ} A {Λ {A₁} M ∙ K} reduce N | .(sub (sub M (A₁ ∷⋯ A ⋯ [ γ ↦ N ]∷⋯ [id])) ([ A₁ ↦ sub K (A ⋯ [ γ ↦ N ]∷⋯ [id]) ]∷⋯ [id])) | refl = reduce ∷✴ ε
  →β-sub-L-g A {Λ {γ} M} {Λ {.γ} M'} (under p) N = 
    →β✴-Λ (→β-sub-L-g (γ ∷ A) p N)
  →β-sub-L-g A (left p) N₁ = 
    →β✴-∙ ε (→β-sub-L-g A p N₁)
  →β-sub-L-g A (right p) N₁ = 
    →β✴-∙ (→β-sub-L-g A p N₁) ε

  →β-sub-L : ∀ {Γ τ γ}
           → {M M' : Term (γ ∷ Γ) τ} → (M →β M')
           → (N : Term Γ γ)
           → sub M [ γ ↦ N ] →β✴ sub M' [ γ ↦ N ]
  →β-sub-L = →β-sub-L-g []

  →β✴-sub-L : ∀ {Γ τ γ}
            → {M M' : Term (γ ∷ Γ) τ}
            → (M →β✴ M')
            → (N : Term Γ γ)
            → sub M [ γ ↦ N ] →β✴ sub M' [ γ ↦ N ]
  →β✴-sub-L ε N = ε
  →β✴-sub-L (x ∷✴ p) N = (→β-sub-L x N) ++✴ →β✴-sub-L p N

  -- Substitution is substitutive for →β✴
  →β✴-sub : ∀ {Γ τ γ}
          → {M M' : Term (γ ∷ Γ) τ} → M →β✴ M'
          → {N N' : Term Γ γ} → N →β✴ N'
          → sub M [ γ ↦ N ] →β✴ sub M' [ γ ↦ N' ]
  →β✴-sub {M' = M'} p1 {N = N} p2 = 
    →β✴-sub-L p1 N ++✴ →β✴-sub-R M' p2

  -- ##### ⇉β-reduction ##### --

  ⇉β-sub-L-g : ∀ {Γ τ γ}
           → (A : Ctx)
           → {M M' : Term (A ++ γ ∷ Γ) τ} → M ⇉β M'
           → (N : Term Γ γ)
           → sub M (A ⋯ [ γ ↦ N ]) ⇉β sub M' (A ⋯ [ γ ↦ N ])
  ⇉β-sub-L-g A parsame N = parsame
  ⇉β-sub-L-g {Γ}{τ}{γ} A {Λ {γ₂} M ∙ N} (parreduce {M' = M'} {N' = N'} p p₁) N₁ with
    sub (sub M' [ γ₂ ↦ N' ]) (A ⋯ [ γ ↦ N₁ ]) |
    lemma-sub M' N' (A ⋯ [ γ ↦ N₁ ]) 
  ⇉β-sub-L-g {Γ} {τ} {γ} A {Λ {A₁} M ∙ N} (parreduce {.τ} {.A₁} {.M} {M'} {.N} {N'} p p₁) N₁ | .(sub (sub M' (A₁ ∷⋯ A ⋯ [ γ ↦ N₁ ]∷⋯ [id])) ([ A₁ ↦ sub N' (A ⋯ [ γ ↦ N₁ ]∷⋯ [id]) ]∷⋯ [id])) | refl = 
    parreduce (⇉β-sub-L-g (A₁ ∷ A) p N₁) (⇉β-sub-L-g A p₁ N₁) 
  ⇉β-sub-L-g A {Λ {γ} M} (parunder p) N = parunder (⇉β-sub-L-g (γ ∷ A) p N)
  ⇉β-sub-L-g A (parapp p p₁) N₁ = parapp (⇉β-sub-L-g A p N₁) (⇉β-sub-L-g A p₁ N₁)

  ⇉β-wk : ∀ {Γ γ}
    → ∀ {Δ} → (f : Γ ⊆ Δ)
    → {N N' : Term Γ γ} → N ⇉β N'
    → wk N f ⇉β wk N' f
  ⇉β-wk f parsame = parsame
  ⇉β-wk {Γ}{γ} f {Λ M ∙ N} (parreduce {γ = γ₁}{M = .M}{M' = M₁'}{N' = N'} p p₁) with
    wk (sub M₁' [ γ₁ ↦ N' ]) f |
    lemma-wk f M₁' N'
  ⇉β-wk {Γ}{γ} f {Λ M ∙ N} (parreduce {γ = γ₁}{M = .M}{M' = M₁'}{N' = N'} p p₁) | .(sub (wk M₁' (γ₁ ∷w⋯ f)) ([ γ₁ ↦ wk N' f ]∷⋯ [id])) | refl = parreduce (⇉β-wk (γ₁ ∷w⋯ f) p) (⇉β-wk f p₁)
  ⇉β-wk {γ = γ₁ →' γ₂} f (parunder p) = parunder (⇉β-wk (γ₁ ∷w⋯ f) p)
  ⇉β-wk f (parapp p p₁) = parapp (⇉β-wk f p) (⇉β-wk f p₁)

  q : ∀ {Γ γ τ}
    → (A : Ctx)
    → ∀ {Δ} → (f : (A ++ Γ) ⊆ Δ)
    → {N N' : Term Γ γ} → (N ⇉β N')
    → (x : τ ∈ (A ++ γ ∷ Γ))
    → wk ((A ⋯ [ γ ↦ N ]) ! x) f ⇉β wk ((A ⋯ [ γ ↦ N' ]) ! x) f
  q [] f p (here refl) = ⇉β-wk f p
  q [] f p (there x) = parsame
  q (_ ∷ _) _ _ (here refl) = parsame
  q (_ ∷ A) f p (there x₁) = ⇉β-wk f (q A there p x₁)

  ⇉β-sub-R-g : ∀ {Γ τ γ}
           → (A : Ctx)
           → (M : Term (A ++ γ ∷ Γ) τ)
           → {N N' : Term Γ γ} → N ⇉β N'
           → sub M (A ⋯ [ γ ↦ N ]) ⇉β sub M (A ⋯ [ γ ↦ N' ])
  ⇉β-sub-R-g A M parsame = parsame
  ⇉β-sub-R-g [] (⋆ here refl) p = p
  ⇉β-sub-R-g [] (⋆ there _) _ = parsame
  ⇉β-sub-R-g (x ∷ A) (⋆ here refl) p = parsame
  ⇉β-sub-R-g A (Λ {γ} M) p = parunder (⇉β-sub-R-g (γ ∷ A) M p)
  ⇉β-sub-R-g A (M ∙ M₁) p = parapp (⇉β-sub-R-g A M p) (⇉β-sub-R-g A M₁ p)
  ⇉β-sub-R-g (x ∷ A) (⋆ there x₁) p = q A there p x₁

  ⇉β-sub-g : ∀ {Γ τ γ}
           → (A : Ctx)
           → {M M' : Term (A ++ γ ∷ Γ) τ} → M ⇉β M'
           → {N N' : Term Γ γ} → N ⇉β N'
           → sub M (A ⋯ [ γ ↦ N ]) ⇉β sub M' (A ⋯ [ γ ↦ N' ])
  ⇉β-sub-g A p1 {N' = N'} parsame = ⇉β-sub-L-g A p1 N'
  ⇉β-sub-g A {M' = M'} parsame p = ⇉β-sub-R-g A M' p
  ⇉β-sub-g A (parunder {γ = γ} p1) p2 = parunder (⇉β-sub-g (γ ∷ A) p1 p2)
  ⇉β-sub-g A (parapp p1 p2) p3 = parapp (⇉β-sub-g A p1 p3) (⇉β-sub-g A p2 p3)
  ⇉β-sub-g {Γ}{τ}{γ} A {Λ {γ₂} M ∙ N} (parreduce {M' = M'}{N' = N'} p1 p2) {N₁}{N₁'} p3 with
    sub (sub M' [ γ₂ ↦ N' ]) (A ⋯ [ γ ↦ N₁' ]) |
    lemma-sub M' N' (A ⋯ [ γ ↦ N₁' ])
  ⇉β-sub-g {Γ} {τ} {γ} A {Λ {A₁} M ∙ N} (parreduce {.τ} {.A₁} {.M} {M'} {.N} {N'} p1 p2) {N₁} {N''} p3 | .(sub (sub M' (A₁ ∷⋯ A ⋯ [ γ ↦ N'' ]∷⋯ [id])) ([ A₁ ↦ sub N' (A ⋯ [ γ ↦ N'' ]∷⋯ [id]) ]∷⋯ [id])) | refl = parreduce (⇉β-sub-g (A₁ ∷ A) p1 p3) (⇉β-sub-g A p2 p3)


  -- Substitution is substitutive for ⇉β
  ⇉β-sub : ∀ {Γ τ γ}
         → {M M' : Term (γ ∷ Γ) τ} → M ⇉β M'
         → {N N' : Term Γ γ} → N ⇉β N'
         → sub M [ γ ↦ N ] ⇉β sub M' [ γ ↦ N' ]
  ⇉β-sub = ⇉β-sub-g []

  -- ⇉β is confluent
  ⇉β-confluent : ∀ {Γ τ} → Confluent {Term Γ τ} _⇉β_
  ⇉β-confluent {c = c} parsame ac = c , ac , parsame
  ⇉β-confluent {b = b} ab parsame = b , parsame , ab
  ⇉β-confluent {a = Λ {γ} a₁ ∙ a₂}(parreduce ab ab₁) (parreduce ac ac₁) with
    ⇉β-confluent ab ac | ⇉β-confluent ab₁ ac₁
  ... | d , fst , snd | d₁ , fst₁ , snd₁ = sub d [ γ ↦ d₁ ] , (⇉β-sub fst fst₁) , ⇉β-sub snd snd₁
  ⇉β-confluent {a = Λ {γ} a₁ ∙ a₂} (parreduce ab ab₁) (parapp {M' = M''} ac ac₁) with 
    ⇉β-confluent ab₁ ac₁
  ⇉β-confluent {Γ} {τ} {Λ a₁ ∙ a₂} (parreduce ab ab₁) (parapp {M' = ⋆ x} () ac₁) | d , p1 , p2
  ⇉β-confluent {Γ} {τ} {Λ {γ} .M'' ∙ a₂} (parreduce {M' = M'} ab ab₁) (parapp {M' = Λ M''} parsame ac₁) | d , p1 , p2 = sub M' [ γ ↦ d ] , (⇉β-sub {Γ}{τ}{γ}{M'} parsame p1) , (parreduce ab p2)
  ⇉β-confluent {Γ} {τ} {Λ {γ} a₁ ∙ a₂} (parreduce ab ab₁) (parapp {M' = Λ M''} (parunder ac) ac₁) | d , p1 , p2 with
      ⇉β-confluent ab ac 
  ... | d₁ , p3 , p4 = sub d₁ [ γ ↦ d ] , (⇉β-sub p3 p1) , (⇉β-sub {Γ}{τ}{τ}{⋆ here refl} parsame (parreduce p4 p2))
  ⇉β-confluent {Γ} {τ} {Λ a₁ ∙ a₂} (parreduce ab ab₁) (parapp {M' = M₁'' ∙ M₂''} () ac₁) | d , p1 , p2
  ⇉β-confluent (parunder ab) (parunder ac) with
    ⇉β-confluent ab ac 
  ... | d , bd , cd = Λ d , parunder bd , parunder cd
  ⇉β-confluent (parapp {M' = Λ {γ} M'} parsame ab₁) (parreduce {M' = M''} ac ac₁) with
    ⇉β-confluent ab₁ ac₁ 
  ... | d₁ , p1 , p2 = sub M'' [ γ ↦ d₁ ] , parreduce ac p1 , (⇉β-sub {M = M''} parsame p2)
  ⇉β-confluent {a = Λ {γ} a₁ ∙ a₂} (parapp (parunder ab) ab₁) (parreduce ac ac₁) with 
    ⇉β-confluent ab ac | ⇉β-confluent ab₁ ac₁ 
  ... | d , p1 , p2 | d₁ , p3 , p4 = sub d [ γ ↦ d₁ ] , (parreduce p1 p3) , (⇉β-sub p2 p4)
  ⇉β-confluent {a = a₁ ∙ a₂}{b₁ ∙ b₂}{c₁ ∙ c₂} (parapp ab ab₁) (parapp ac ac₁) with 
    ⇉β-confluent ab ac | ⇉β-confluent ab₁ ac₁ 
  ... | d , b₂d , c₁d | d₁ , b₂d₁ , c₂d₁ = 
    d ∙ d₁ , (parapp b₂d b₂d₁) , (parapp c₁d c₂d₁)

  -- Transformations between →β✴ and ⇉β✴ show that they are equivalent:

  →β-⇉β : ∀ {Γ τ} {M N : Term Γ τ} → M →β N → M ⇉β N
  →β-⇉β reduce = parreduce parsame parsame
  →β-⇉β (under x) = parunder (→β-⇉β x)
  →β-⇉β (left x) = parapp (→β-⇉β x) parsame
  →β-⇉β (right x) = parapp parsame (→β-⇉β x)

  →β-⇉β✴ : ∀ {Γ τ} {M N : Term Γ τ} → M →β✴ N → M ⇉β✴ N
  →β-⇉β✴ = map✴ id →β-⇉β

  ⇉β-→β : ∀ {Γ τ} {M N : Term Γ τ} → M ⇉β N → M →β✴ N
  ⇉β-→β parsame = ε
  ⇉β-→β (parreduce mn mn₁) = reduce ∷✴ →β✴-sub (⇉β-→β mn) (⇉β-→β mn₁) 
  ⇉β-→β (parunder mn) = map✴ Λ under (⇉β-→β mn)
  ⇉β-→β {M = M ∙ M'}{N = N ∙ N'} (parapp mn mn₁) = 
    map✴ (λ z → z ∙ M') left (⇉β-→β mn) 
    ++✴ map✴ (_∙_ N) right (⇉β-→β mn₁)

  ⇉β-→β✴ : ∀ {Γ τ} {M N : Term Γ τ} → M ⇉β✴ N → M →β✴ N
  ⇉β-→β✴ = concat✴ ∘ map✴ id ⇉β-→β

  -- →β✴ is confluent
  →β✴-confluent : ∀ {Γ τ} → Confluent (_→β✴_ {Γ = Γ} {τ = τ})
  →β✴-confluent ra rx with CR ⇉β-confluent (→β-⇉β✴ ra) (→β-⇉β✴ rx)
  ... | L , (rb , ry) = L , (⇉β-→β✴ rb , ⇉β-→β✴ ry)

