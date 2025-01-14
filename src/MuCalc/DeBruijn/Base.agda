module MuCalc.DeBruijn.Base where

open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties using (m≤n⇒m≤1+n; ≤-refl; ≤-trans)
open import Data.Fin as F using (Fin; _≟_) renaming (_ℕ-ℕ_ to _-_)
open import Data.Empty renaming (⊥ to Zero)
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Decidable

--------------------------------------------------------------

data Opη : Set where
  mu : Opη
  nu : Opη

data Op₀ (At : Set) : Set where
  tt : Op₀ At
  ff : Op₀ At
  at  : At → Op₀ At
  ¬at : At → Op₀ At

data Op₁ : Set where
  box : Op₁
  dia : Op₁

data Op₂ : Set where
  and : Op₂
  or : Op₂

-- Formulas are parameterised by the list of names in scope.
data μML (At : Set) (n : ℕ) : Set where
  var : Fin n → μML At n
  μML₀ : (op : Op₀ At) → μML At n
  μML₁ : (op : Op₁) → (ϕ : μML At n) → μML At n
  μML₂ : (op : Op₂) → (ϕ : μML At n) → (ψ : μML At n) → μML At n
  μMLη : (op : Opη) → (ϕ : μML At (suc n)) → μML At n

data IsFP {At : Set} : {n : ℕ} (ϕ : μML At n) → Set where
  instance fp : {n : ℕ} {op : Opη} {ψ : μML At (suc n)} → IsFP (μMLη op ψ)

-- Some prettier pattern synonyms
pattern ⊤ = μML₀ tt
pattern ⊥ = μML₀ ff
pattern lit x = μML₀ (at x)
pattern ¬lit x = μML₀ (¬at x)
pattern ■ ϕ = μML₁ box ϕ
pattern ◆ ϕ = μML₁ dia ϕ
pattern _∧_ ϕ ψ = μML₂ and ϕ ψ
pattern _∨_ ϕ ψ = μML₂ or ϕ ψ
pattern μ ϕ = μMLη mu ϕ
pattern ν ϕ = μMLη nu ϕ


--------------------------------------------------------------

-- -- Negation is derived by de Morgan substitutions.
-- ¬ : ∀ {At n} → μML At n → μML At n
-- ¬ (var x)        = var x -- is this right?
-- ¬ ⊤ = ⊥
-- ¬ ⊥ = ⊤
-- ¬ (μML₀ (at x)) = μML₀ (¬at x)
-- ¬ (μML₀ (¬at x)) = μML₀ (at x)
-- ¬ (■ ϕ) = ◆ (¬ ϕ)
-- ¬ (◆ ϕ) = ■ (¬ ϕ)
-- ¬ (ϕ ∧ ψ) = (¬ ϕ) ∨ (¬ ψ)
-- ¬ (ϕ ∨ ψ) = (¬ ϕ) ∧ (¬ ψ)
-- ¬ (μ ϕ) = ν (¬ ϕ)
-- ¬ (ν ϕ) = μ (¬ ϕ)

-- -- Material implication
-- _⇒_ : ∀ {At n} → μML At n → μML At n → μML At n
-- ϕ ⇒ ψ = μML₂ or (¬ ϕ) ψ


--------------------------------------------------------------
-- Substitution --

-- Scope extension
ext : ∀ {n m} → (Fin n → Fin m)
    → Fin (suc n) → Fin (suc m)
ext ρ F.zero = F.zero
ext ρ (F.suc x) = F.suc (ρ x)

-- Rescoping
rescope : ∀ {At n m} → (Fin n → Fin m) -- if we have an mapping of i vars to j vars...
        → μML At n → μML At m -- then we can rescope i-terms to be j-terms.
rescope ρ (var x) = var (ρ x)
rescope ρ (μML₀ op) = μML₀ op
rescope ρ (μML₁ op ϕ) = μML₁ op (rescope ρ ϕ)
rescope ρ (μML₂ op ϕ ψ) = μML₂ op (rescope ρ ϕ) (rescope ρ ψ)
rescope ρ (μMLη op ϕ) = μMLη op (rescope (ext ρ) ϕ)

-- Parallel substitutions are maps from variables to formulae
Subst : Set → ℕ → ℕ → Set
Subst At n m = Fin n → μML At m

-- Substitution extension
exts : ∀ {At n m} → Subst At n m → Subst At (suc n) (suc m)
exts σ F.zero = var F.zero
exts σ (F.suc x) = rescope F.suc (σ x)

-- Executing a parallel substitution
sub : ∀ {At n m} → Subst At n m → μML At n → μML At m
sub σ (var x) = σ x
sub σ (μML₀ op) = μML₀ op
sub σ (μML₁ op ϕ) = μML₁ op (sub σ ϕ)
sub σ (μML₂ op ϕ ψ) = μML₂ op (sub σ ϕ) (sub σ ψ)
sub σ (μMLη op ϕ) = μMLη op (sub (exts σ) ϕ)

-- Single substitution is a special case of parallel substitution
sub₀ : ∀ {At n} → μML At n → Subst At (suc n) n
sub₀ ϕ F.zero = ϕ -- at 0 we substitute
sub₀ ϕ (F.suc x) = var x -- elsewhere we leave step the variable

_[_] : ∀ {At n} → μML At (suc n) → μML At n → μML At n
ϕ [ δ ] = sub (sub₀ δ) ϕ

-- And now fixpoint unfolding is a single substitution
opaque -- opaque only temporarily to make some types easier to read
  unfold : ∀ {At n} (ϕ : μML At n) → {{_ : IsFP ϕ}} → μML At n
  unfold (μMLη op ψ) = ψ [ μMLη op ψ ]


---------------------------------
-- Weakening and Strengthening --
---------------------------------

-- Thinnings!
-- AKA monotone embedding of Fin i to Fin j.
-- AKA bit vectors.
data Thin : ℕ → ℕ → Set where
  keep : ∀ {i j} → Thin i j → Thin (suc i) (suc j) -- 1 ∷_
  drop : ∀ {i j} → Thin i j → Thin i (suc j)       -- 0 ∷_
  end : Thin 0 0                                   -- ε

-- The identity thinning; all 1's.
full : ∀ {i} → Thin i i
full {zero} = end
full {suc i} = keep full

-- Turning a thinning into an actual embedding of variables
embed : {i j : ℕ} → Thin i j → Fin i → Fin j
embed (keep θ) F.zero = F.zero
embed (keep θ) (F.suc x) = F.suc (embed θ x)
embed (drop θ) x = F.suc (embed θ x)

-- The identity thinning really is identity
embed-full : ∀ {i} (x : Fin i) → embed full x ≡ x
embed-full F.zero = refl
embed-full (F.suc x) = cong F.suc (embed-full x)

weaken : ∀ {At i j} → Thin i j → μML At i → μML At j
weaken θ = rescope (embed θ)

weaken₁ : ∀ {At i} → μML At i → μML At (suc i)
weaken₁ = weaken (drop full)

-- Paths through formulas to variables
data VarOccurs {At : Set} {n : ℕ} (x : Fin n) : (ϕ : μML At n) → Set where
  here  : VarOccurs x (var x)
  down  : ∀ {op ϕ} → VarOccurs x ϕ → VarOccurs x (μML₁ op ϕ)
  left  : ∀ {op ϕ ψ} → VarOccurs x ϕ → VarOccurs x (μML₂ op ϕ ψ)
  right : ∀ {op ϕ ψ} → VarOccurs x ψ → VarOccurs x (μML₂ op ϕ ψ)
  under : ∀ {op ϕ} → VarOccurs (F.suc x) ϕ → VarOccurs x (μMLη op ϕ) -- increment when traversing a binder

-- Either a variable doesn't occur, or we can find a path to where it does.
var-occurs? : ∀ {At n} (x : Fin n) (ϕ : μML At n) → Dec (VarOccurs x ϕ)
var-occurs? x (var y) = map′ (λ {refl → here}) (λ { here → refl}) (x ≟ y)
var-occurs? x (μML₀ op) = no (λ ())
var-occurs? x (μML₁ op ϕ) = map′ down (λ {(down p) → p}) (var-occurs? x ϕ)
var-occurs? x (μML₂ op ϕ ψ) with var-occurs? x ϕ | var-occurs? x ψ
... | yes p | _ = yes (left p)
... | no ¬p | yes q = yes (right q)
... | no ¬p | no ¬q = no λ { (left p) → ¬p p ; (right q) → ¬q q}
var-occurs? x (μMLη op ϕ) = map′ under (λ {(under p) → p}) (var-occurs? (F.suc x) ϕ)

-- Whether a given variable supported (marked as keep) by a thinning
data Supported : {i j : ℕ} → Thin i j → Fin j → Set where
  here : ∀ {i j} {θ : Thin i j} → Supported (keep θ) F.zero
  there-k : ∀ {i j} {θ : Thin i j} {x : Fin j} → Supported θ x → Supported (keep θ) (F.suc x)
  there-d : ∀ {i j} {θ : Thin i j} {x : Fin j} → Supported θ x → Supported (drop θ) (F.suc x)

{-
-- The support of a formula is the number of free variables that actually occur, not just
-- the number that are in scope. We can traverse a formula to compute its support.
-- Even better than knowing the mere number is having a thinning that tells us /which/
-- variables occur.
support-size : ∀ {At n} → μML At n → ℕ
support : ∀ {At n} → (ϕ : μML At n) → Thin (support-size ϕ) n

support-size ϕ = {!!}
support = {!!}

support-occurs? : ∀ {At n} → (ϕ : μML At n) → Dec (∀ (x : Fin n) → Supported (support ϕ) x → VarOccurs x ϕ)
support-occurs? = {!!}

-- We can strengthen the scope of any formula to at most the size of its support.
strengthen : ∀ {At i j} → Thin i j → (ϕ : μML At j) → Thin (support-size ϕ) i → μML At i
strengthen = {!!}

-}

--------------------------------
-- Properties of Substitution --
--  (and related machinery)   --
--------------------------------

rescope-preserves-fp : ∀ {At n m} → {ρ : Fin n → Fin m} → (ϕ : μML At n) → {{_ : IsFP ϕ}} → IsFP (rescope ρ ϕ)
rescope-preserves-fp (μMLη op ϕ) = fp

subs-agree : ∀ {At n m}
           → (σ θ : Subst At n m) -- Given two substitutions...
           → (ϕ : μML At n) -- and some formula...
           → (∀ {x} → VarOccurs x ϕ → σ x ≡ θ x) -- if the two substitutions agree on all of those variables that occur in the formula...
           → sub σ ϕ ≡ sub θ ϕ -- Then the substitutions really do agree for that formula.
subs-agree σ θ (var x) eq = eq here
subs-agree σ θ (μML₀ op) eq = refl
subs-agree σ θ (μML₁ op ϕ) eq = cong (μML₁ op) (subs-agree σ θ ϕ (λ [x] → eq (down [x])))
subs-agree σ θ (μML₂ op ϕ ψ) eq = cong₂ (μML₂ op) (subs-agree σ θ ϕ (λ [x] → eq (left [x]))) (subs-agree σ θ ψ λ [x] → eq (right [x]))
subs-agree σ θ (μMLη op ϕ) eq = cong (μMLη op) (subs-agree (exts σ) (exts θ) ϕ (λ { {F.zero} [x] → refl ; {F.suc x} [x] → cong (rescope F.suc) (eq (under [x]))}))

-- The identity substitution
IdSubst : ∀ {At n} → Subst At n n
IdSubst = var

IdSubst-ext : ∀ {At n} {σ : Subst At n n} → σ ≗ IdSubst → (exts σ ≗ IdSubst)
IdSubst-ext eq F.zero = refl
IdSubst-ext {At} {n} {σ} eq (F.suc x) = cong (rescope F.suc) (eq x)

-- The identity substitution (up to potintwise-equality) really is identity
sub-id : ∀ {At n σ} → (ϕ : μML At n) → (σ ≗ IdSubst) → sub σ ϕ ≡ ϕ
sub-id (var x) eq = eq x
sub-id (μML₀ op) eq = refl
sub-id (μML₁ op ϕ) eq = cong (μML₁ op) (sub-id ϕ eq)
sub-id (μML₂ op ϕ ψ) eq = cong₂ (μML₂ op) (sub-id ϕ eq) (sub-id ψ eq)
sub-id (μMLη op ϕ) eq = cong (μMLη op) (sub-id ϕ (IdSubst-ext eq))

-- Weakened id substitutions
WeakIdSubst : ∀ {At i j} → Thin i j → Subst At i j
WeakIdSubst θ x = weaken θ (var x)

{-
-- Weakening (by 1) and substitution commute.
sub-weaken : ∀ {At i j} → (σ : Subst At i j) (ϕ : μML At i)
           → (sub (exts σ) (weaken₁ ϕ)) ≡ weaken₁ (sub σ ϕ)
sub-weaken σ ϕ = {!!}

-- Putting all the above together in the special case of a single substitution:
-- If the variable being substituted doesn't appear, the substitution is identity(ish)
sub-trivial : ∀ {At n}
            → (ϕ : μML At (suc n)) (δ : μML At n)
            → (p : ¬ (VarOccurs F.zero ϕ))
            → weaken₁ (ϕ [ δ ]) ≡ ϕ
sub-trivial ϕ δ p = begin
  weaken₁ (ϕ [ δ ])
  ≡⟨ (sym $ sub-weaken (sub₀ δ) ϕ) ⟩
  sub (exts (sub₀ δ)) (weaken₁ ϕ)
  ≡⟨ {!subs-agree!} ⟩
  sub {!IdSubst!} (weaken₁ ϕ) -- does there exist an identityish subst with this type? If not, need a version of subs-agree for weakenings which would subsume these two steps
  ≡⟨ {!substid-weaken!} ⟩
  sub IdSubst ϕ
  ≡⟨ sub-id ϕ (λ _ → refl) ⟩
  ϕ
  ∎ where open ≡-Reasoning
-}

-----------------
-- Subformulas --
-----------------

-- The proper (ie, irreflexive) subformula relation.
-- ψ ⊐ ϕ ==> ϕ is a proper sf of ψ.
data _⊐_ {At : Set} : {i j : ℕ} → (ψ : μML At i) (ϕ : μML At j) → {{i ≤ j}} → Set where
  down  : ∀ op {i j} {p : i ≤ j} {ψ : μML At i} {ϕ : μML At j} → (ψ ⊐ ϕ) {{p}} → (ψ ⊐ (μML₁ op ϕ)) {{p}}
  left  : ∀ op {i j} {p : i ≤ j} {ψ : μML At i} {ϕˡ ϕʳ : μML At j} → (ψ ⊐ ϕˡ) {{p}} → (ψ ⊐ (μML₂ op ϕˡ ϕʳ)) {{p}}
  right : ∀ op {i j} {p : i ≤ j} {ψ : μML At i} {ϕˡ ϕʳ : μML At j} → (ψ ⊐ ϕʳ) {{p}} → (ψ ⊐ (μML₂ op ϕˡ ϕʳ)) {{p}}
  under : ∀ op {i j} {p : i ≤ j} {ψ : μML At i} {ϕ : μML At (suc j)} → (ψ ⊐ ϕ) {{m≤n⇒m≤1+n p}} → (ψ ⊐ (μMLη op ϕ)) {{p}}

-- -- The membership relation for the subformula set is the reflexive transitive closure of _⊐_.
-- -- In other words, ⊐-paths. The stdlib version doesn't fit here because of the way we treat the indices.
-- data _∈SF_ {At : Set} : {i j : ℕ} → (ψ : μML At i) (ϕ : μML At j) → {{i ≤ j}} → Set where
--   ε : ∀ {i} {ϕ : μML At i} → (ϕ ∈SF ϕ) {{≤-refl}}
--   _◅_ : ∀ {i j k} {p : i ≤ j} {q : j ≤ k} {ξ : μML At i} {ψ : μML At j} {ϕ : μML At k}
--       → (ξ ⊐ ψ) {{p}} → (ψ ∈SF ϕ) {{q}} → (ξ ∈SF ϕ) {{≤-trans p q}}

-- -- We need to carry around a bunch of indices to form the subformula set, unfortunately
-- -- (unless we want the...i≤n-indexed suformula family...?)
-- Sfor : {At : Set} {n : ℕ} → μML At n → Set
-- Sfor {At} {n} ϕ = Σ[ i ∈ ℕ ] Σ[ p ∈ i ≤ n ] Σ[ ψ ∈ μML At i ] ((ψ ∈SF ϕ) {{p}})

-------------
--  Scopes --
-------------

-- Vectors of formulas, with two added tricks:
-- * The index of the formula depends on its position in the vector
-- * We allow the front of the scope to potentially coontain dummies. This is to faciliatate the definition of the expansion map,
--   where we want to instantiate variables that were already free but leave previously bound variables alone.
data Scope (At : Set) : ℕ → Set where
  [] : Scope At zero
  _,-_ : ∀ {n} → (ϕ : μML At n) (Γ : Scope At n) → Scope At (suc n)

lookup : ∀ {At n} → (Γ : Scope At n) → (x : Fin n) → μML At (n - (F.suc x))
lookup (ϕ ,- Γ) F.zero = ϕ
lookup (ϕ ,- Γ) (F.suc x) = lookup Γ x

unwind : ∀ {At n} → (Γ : Scope At n) → (x : Fin n) → Scope At (n - (F.suc x))
unwind (ϕ ,- Γ) F.zero = Γ
unwind (ϕ ,- Γ) (F.suc x) = unwind Γ x
