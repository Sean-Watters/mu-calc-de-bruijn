{-# OPTIONS --safe #-}
module MuCalc.Syntax.Substitution where

open import Data.Nat
open import Data.Fin as F using (Fin)
open import Data.Product
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

open import MuCalc.Base

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
sub₀ ϕ (F.suc x) = var x

_[_] : ∀ {At n} → μML At (suc n) → μML At n → μML At n
ϕ [ δ ] = sub (sub₀ δ) ϕ

-- And now fixpoint unfolding is a single substitution
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
var-occurs? x (var y) = map′ (λ {refl → here}) (λ { here → refl}) (x F.≟ y)
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

-------------------------
-- Single Substitution --
-------------------------

data IsSingleSub {At : Set} {n m : ℕ} (σ : Subst At n m) : Set where
  aye : (x : Fin n) → {ϕ : μML At m} → σ x ≡ ϕ               -- There's one variable that goes to whatever ϕ you like...
      → (∀ (y : Fin n) → y ≢ x → Σ[ z ∈ Fin m ] σ y ≡ var z) -- ...meanwhile the others all go to variables.
      → IsSingleSub σ

-- Single substitution is a single substitution. Duh.
singlesub : ∀ {At n} → (ϕ : μML At n) → IsSingleSub (sub₀ ϕ)
singlesub {At} {n} ϕ = aye F.zero refl v where
  v : (y : Fin (suc n)) → y ≢ F.zero → Σ[ z ∈ Fin n ] (sub₀ ϕ y ≡ var z)
  v F.zero ne = ⊥-elim (ne refl)
  v (F.suc y) ne = y , refl
