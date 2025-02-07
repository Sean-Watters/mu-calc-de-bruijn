{-# OPTIONS --safe #-}
module MuCalc.Syntax.Substitution where

open import Data.Nat
open import Data.Fin as F using (Fin)
open import Data.Product
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

open import Function using (_∘_; _$_; id)

open import MuCalc.Base

---------------------------
-- Parallel Substitution --
---------------------------

-- Renamings are maps of variables
Rename : ℕ → ℕ → Set
Rename n m = Fin n → Fin m

-- Parallel substitutions are maps from variables to formulae
Subst : Set → ℕ → ℕ → Set
Subst At n m = Fin n → μML At m

-- Renaming extension
ext : ∀ {n m} → Rename n m → Rename (suc n) (suc m)
ext ρ F.zero = F.zero
ext ρ (F.suc x) = F.suc (ρ x)

-- Executing a renaming
rename : ∀ {At n m} → Rename n m -- if we have an mapping of n vars to m vars...
        → μML At n → μML At m -- then we can rename n-terms to be m-terms.
rename ρ (var x) = var (ρ x)
rename ρ (μML₀ op) = μML₀ op
rename ρ (μML₁ op ϕ) = μML₁ op (rename ρ ϕ)
rename ρ (μML₂ op ϕ ψ) = μML₂ op (rename ρ ϕ) (rename ρ ψ)
rename ρ (μMLη op ϕ) = μMLη op (rename (ext ρ) ϕ)

-- Substitution extension
exts : ∀ {At n m} → Subst At n m → Subst At (suc n) (suc m)
exts σ F.zero = var F.zero
exts σ (F.suc x) = rename F.suc (σ x)

-- Executing a parallel substitution
sub : ∀ {At n m} → Subst At n m → μML At n → μML At m
sub σ (var x) = σ x
sub σ (μML₀ op) = μML₀ op
sub σ (μML₁ op ϕ) = μML₁ op (sub σ ϕ)
sub σ (μML₂ op ϕ ψ) = μML₂ op (sub σ ϕ) (sub σ ψ)
sub σ (μMLη op ϕ) = μMLη op (sub (exts σ) ϕ)

-------------------------
-- Single Substitution --
-------------------------

-- Single substitution: sub in ϕ at 0, and decrement all other variables by 1
sub₀ : ∀ {At n} → μML At n → Subst At (suc n) n
sub₀ ϕ F.zero = ϕ -- at 0 we substitute
sub₀ ϕ (F.suc x) = var x

-- Single substitution is a special case of parallel substitution
_[_] : ∀ {At n} → μML At (suc n) → μML At n → μML At n
ϕ [ δ ] = sub (sub₀ δ) ϕ

-- Single substitution at index 1
_[_]' : ∀ {At n} → μML At (2+ n) → μML At n → μML At (suc n)
ϕ [ δ ]' = sub (exts (sub₀ δ)) ϕ

-- And now fixpoint unfolding is a single substitution
unfold : ∀ {At n} (ϕ : μML At n) → {{_ : IsFP ϕ}} → μML At n
unfold (μMLη op ψ) = ψ [ μMLη op ψ ]


-------------------------------
-- Some Useful Substitutions --
-------------------------------

-- The identity substitution.
ids : ∀ {At n} → Subst At n n
ids x = var x

-- Substitution composition
_⨾_ : ∀ {At i j k} → Subst At i j → Subst At j k → Subst At i k
σ ⨾ τ = (sub τ) ∘ σ


-----------------------------------
-- The Fusion Lemma for Renaming --
-----------------------------------

ext-eq : ∀ {i j} {ρ ρ' : Rename i j}
       → ρ ≗ ρ'
       → ext ρ ≗ ext ρ'
ext-eq eq F.zero = refl
ext-eq eq (F.suc x) = cong F.suc (eq x)

rename-cong : ∀ {At i j} {ρ ρ' : Rename i j}
            → ρ ≗ ρ'
            → rename {At} ρ ≗ rename ρ'
rename-cong eq (var x) = cong var (eq x)
rename-cong eq (μML₀ op) = refl
rename-cong eq (μML₁ op ϕ) = cong (μML₁ op) (rename-cong eq ϕ)
rename-cong eq (μML₂ op ϕl ϕr) = cong₂ (μML₂ op) (rename-cong eq ϕl) (rename-cong eq ϕr)
rename-cong eq (μMLη op ϕ) = cong (μMLη op) (rename-cong (ext-eq eq) ϕ)

ext-fusion : ∀ {i j k} {ρ1 : Rename j k} {ρ2 : Rename i j} {ρ3 : Rename i k}
           → ρ1 ∘ ρ2 ≗ ρ3
           → (ext ρ1) ∘ (ext ρ2) ≗ ext ρ3
ext-fusion eq F.zero = refl
ext-fusion eq (F.suc x) = cong F.suc (eq x)

rename-fusion : ∀ {At i j k} {ρ1 : Rename j k} {ρ2 : Rename i j} {ρ3 : Rename i k}
              → ρ1 ∘ ρ2 ≗ ρ3
              → (rename {At} ρ1) ∘ (rename ρ2) ≗ rename ρ3
rename-fusion eq (var x) = cong var (eq x)
rename-fusion eq (μML₀ op) = refl
rename-fusion eq (μML₁ op ϕ) = cong (μML₁ op) (rename-fusion eq ϕ)
rename-fusion eq (μML₂ op ϕl ϕr) = cong₂ (μML₂ op) (rename-fusion eq ϕl) (rename-fusion eq ϕr)
rename-fusion eq (μMLη op ϕ) = cong (μMLη op) (rename-fusion (λ x → trans (ext-fusion (λ _ → refl) x) (ext-eq eq x)) ϕ)



------------------------------------------------
-- The Fusion Lemma for Parallel Substitution --
------------------------------------------------

exts-eq : ∀ {At i j} {σ σ' : Subst At i j}
        → σ ≗ σ'
        → exts σ ≗ exts σ'
exts-eq eq F.zero = refl
exts-eq eq (F.suc x) = cong (rename F.suc) (eq x)

sub-cong : ∀ {At i j} {σ σ' : Subst At i j}
         → σ ≗ σ'
         → sub σ ≗ sub σ'
sub-cong eq (var x) = eq x
sub-cong eq (μML₀ op) = refl
sub-cong eq (μML₁ op ϕ) = cong (μML₁ op) (sub-cong eq ϕ)
sub-cong eq (μML₂ op ϕl ϕr) = cong₂ (μML₂ op) (sub-cong eq ϕl) (sub-cong eq ϕr)
sub-cong eq (μMLη op ϕ) = cong (μMLη op) (sub-cong (exts-eq eq) ϕ)

-- Commutativity of renaming by suc.
rename-ext : ∀ {At i j} (ρ : Rename i j)
            → rename {At} F.suc ∘ rename ρ ≗ rename (ext ρ) ∘ rename F.suc
rename-ext ρ ϕ =
  begin
    (rename F.suc ∘ rename ρ) ϕ
  ≡⟨ rename-fusion (λ _ → refl) ϕ ⟩
    rename (F.suc ∘ ρ) ϕ
  ≡⟨ rename-cong (λ _ → refl) ϕ ⟩
    rename (ext ρ ∘ F.suc) ϕ
  ≡⟨ (sym $ rename-fusion (λ _ → refl) ϕ) ⟩
    (rename (ext ρ) ∘ rename F.suc) ϕ
  ∎ where open ≡-Reasoning


exts-rename : ∀ {At} {i} {j} {σ : Subst At i j} {ρ1 : Rename i (suc i)} {ρ2 : Rename j (suc j)}
            → exts σ ∘ ρ1 ≗ rename ρ2 ∘ σ
            → exts (exts σ) ∘ ext ρ1 ≗ rename (ext ρ2) ∘ exts σ
exts-rename eq F.zero = refl
exts-rename {σ = σ} {ρ2 = ρ2} eq (F.suc x) = trans (cong (rename F.suc) (eq x)) (rename-ext ρ2 (σ x))

sub-rename-comm : ∀ {At i j} {σ : Subst At i j} {ρ1 : Rename i (suc i)} {ρ2 : Rename j (suc j)}
                → exts σ ∘ ρ1 ≗ rename ρ2 ∘ σ
                → sub (exts σ) ∘ rename ρ1 ≗ rename ρ2 ∘ sub σ
sub-rename-comm eq (var x) = eq x
sub-rename-comm eq (μML₀ op) = refl
sub-rename-comm eq (μML₁ op ϕ) = cong (μML₁ op) (sub-rename-comm eq ϕ)
sub-rename-comm eq (μML₂ op ϕl ϕr) = cong₂ (μML₂ op) (sub-rename-comm eq ϕl) (sub-rename-comm eq ϕr)
sub-rename-comm eq (μMLη op ϕ) = cong (μMLη op) (sub-rename-comm (exts-rename eq) ϕ)

exts-fusion : ∀ {At i j k} {σ1 : Subst At j k} {σ2 : Subst At i j} {σ3 : Subst At i k}
            → σ2 ⨾ σ1 ≗ σ3
            → exts σ2 ⨾ exts σ1 ≗ exts σ3
exts-fusion eq F.zero = refl
exts-fusion {σ1 = σ1} {σ2} {σ3} eq (F.suc x) = trans (sub-rename-comm (λ _ → refl) (σ2 x)) (cong (rename F.suc) (eq x))

sub-fusion : ∀ {At i j k} {σ1 : Subst At j k} {σ2 : Subst At i j} {σ3 : Subst At i k}
           → σ2 ⨾ σ1 ≗ σ3
           → sub σ1 ∘ sub σ2 ≗ sub σ3
sub-fusion eq (var x) = eq x
sub-fusion eq (μML₀ op) = refl
sub-fusion eq (μML₁ op ϕ) = cong (μML₁ op) (sub-fusion eq ϕ)
sub-fusion eq (μML₂ op ϕl ϕr) = cong₂ (μML₂ op) (sub-fusion eq ϕl) (sub-fusion eq ϕr)
sub-fusion eq (μMLη op ϕ) = cong (μMLη op) (sub-fusion (exts-fusion eq) ϕ)


----------------------------------------------
-- Barendregt's (Single) Substitution Lemma --
----------------------------------------------

sub-rename-id : ∀ {At i j} (ρ : Rename i j) (σ : Subst At j i)
              → var ≗ σ ∘ ρ -- If σ ∘ ρ maps to a var...
              → (ϕ : μML At i) → ϕ ≡ sub σ (rename ρ ϕ) -- ...then applying σ after ρ is the identity.
sub-rename-id ρ σ f (var y) = f y
sub-rename-id ρ σ f (μML₀ op) = refl
sub-rename-id ρ σ f (μML₁ op ϕ) = cong (μML₁ op) (sub-rename-id ρ σ f ϕ)
sub-rename-id ρ σ f (μML₂ op ϕl ϕr) = cong₂ (μML₂ op) (sub-rename-id ρ σ f ϕl) (sub-rename-id ρ σ f ϕr)
sub-rename-id ρ σ f (μMLη op ϕ) = cong (μMLη op) (sub-rename-id (ext ρ) (exts σ) ext-lem ϕ) where
  ext-lem : var ≗ exts σ ∘ ext ρ
  ext-lem F.zero = refl
  ext-lem (F.suc x) = cong (rename F.suc) (f x)


sub₀-compose : ∀ {At n m} → (σ : Subst At n m) (ϕ : μML At (suc n)) (ψ : μML At n)
             → sub₀ ψ ⨾ σ ≗ exts σ ⨾ sub₀ (sub σ ψ)
sub₀-compose σ ϕ ψ F.zero = refl
sub₀-compose σ ϕ ψ (F.suc x) = sub-rename-id F.suc (sub₀ (sub σ ψ)) (λ _ → refl) (σ x)

-- Barendregt's substitution lemma, generalised a little. Substitution commutes with itself.
sub-comm : ∀ {At n m} → (σ : Subst At n m) (ϕ : μML At (suc n)) (ψ : μML At n)
             → sub σ (ϕ [ ψ ]) ≡ (sub (exts σ) ϕ) [ sub σ ψ ]
sub-comm σ ϕ ψ =
  begin
    sub σ (sub (sub₀ ψ) ϕ)
  ≡⟨ sub-fusion (λ _ → refl) ϕ ⟩
    sub (sub₀ ψ ⨾ σ) ϕ
  ≡⟨ sub-cong (sub₀-compose σ ϕ ψ) ϕ ⟩
    sub (exts σ ⨾ sub₀ (sub σ ψ)) ϕ
  ≡⟨ (sym $ sub-fusion (λ _ → refl) ϕ) ⟩
    sub (sub₀ (sub σ ψ)) (sub (exts σ) ϕ)
  ∎ where open ≡-Reasoning

-- Barendregt's substitution lemma
substitution-lemma : ∀ {At i} (ϕ : μML At (2+ i)) (ψ : μML At (suc i)) (ξ : μML At i)
                   → (ϕ [ ψ ]) [ ξ ] ≡ (ϕ [ ξ ]') [ ψ [ ξ ] ]
substitution-lemma ϕ ψ ξ = sub-comm (sub₀ ξ) ϕ ψ

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
weaken θ = rename (embed θ)

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

--------------------------------------
-- Other Properties of Substitution --
--     (and related machinery)      --
--------------------------------------

rename-preserves-fp : ∀ {At n m} → {ρ : Rename n m} → (ϕ : μML At n) → {{_ : IsFP ϕ}} → IsFP (rename ρ ϕ)
rename-preserves-fp (μMLη op ϕ) = fp

subs-agree : ∀ {At n m}
           → (σ θ : Subst At n m) -- Given two substitutions...
           → (ϕ : μML At n) -- and some formula...
           → (∀ {x} → VarOccurs x ϕ → σ x ≡ θ x) -- if the two substitutions agree on all of those variables that occur in the formula...
           → sub σ ϕ ≡ sub θ ϕ -- Then the substitutions really do agree for that formula.
subs-agree σ θ (var x) eq = eq here
subs-agree σ θ (μML₀ op) eq = refl
subs-agree σ θ (μML₁ op ϕ) eq = cong (μML₁ op) (subs-agree σ θ ϕ (λ [x] → eq (down [x])))
subs-agree σ θ (μML₂ op ϕ ψ) eq = cong₂ (μML₂ op) (subs-agree σ θ ϕ (λ [x] → eq (left [x]))) (subs-agree σ θ ψ λ [x] → eq (right [x]))
subs-agree σ θ (μMLη op ϕ) eq = cong (μMLη op) (subs-agree (exts σ) (exts θ) ϕ (λ { {F.zero} [x] → refl ; {F.suc x} [x] → cong (rename F.suc) (eq (under [x]))}))

ids-ext : ∀ {At n} {σ : Subst At n n} → σ ≗ ids → (exts σ ≗ ids)
ids-ext eq F.zero = refl
ids-ext {At} {n} {σ} eq (F.suc x) = cong (rename F.suc) (eq x)

-- The identity substitution (up to potintwise-equality) really is identity
sub-id : ∀ {At n σ} → (ϕ : μML At n) → (σ ≗ ids) → sub σ ϕ ≡ ϕ
sub-id (var x) eq = eq x
sub-id (μML₀ op) eq = refl
sub-id (μML₁ op ϕ) eq = cong (μML₁ op) (sub-id ϕ eq)
sub-id (μML₂ op ϕ ψ) eq = cong₂ (μML₂ op) (sub-id ϕ eq) (sub-id ψ eq)
sub-id (μMLη op ϕ) eq = cong (μMLη op) (sub-id ϕ (ids-ext eq))

-- Weakened id substitutions
Weakids : ∀ {At i j} → Thin i j → Subst At i j
Weakids θ x = weaken θ (var x)

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
  sub {!ids!} (weaken₁ ϕ) -- does there exist an identityish subst with this type? If not, need a version of subs-agree for weakenings which would subsume these two steps
  ≡⟨ {!substid-weaken!} ⟩
  sub ids ϕ
  ≡⟨ sub-id ϕ (λ _ → refl) ⟩
  ϕ
  ∎ where open ≡-Reasoning
-}

