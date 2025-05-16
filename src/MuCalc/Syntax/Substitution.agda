{-# OPTIONS --safe #-}
module MuCalc.Syntax.Substitution where

open import Data.Nat
open import Data.Fin as F using (Fin)
open import Data.Product hiding (map)
open import Data.Empty
open import Data.Sum
open import Data.Thinning.Base as Th using (Thin; embed; inj; pad; end)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

open import Function using (_∘_; _$_; id)

open import Data.Fin.Renaming
open import MuCalc.Base

---------------------------
-- Parallel Substitution --
---------------------------

-- Parallel substitutions are maps from variables to formulae
Subst : Set → ℕ → ℕ → Set
Subst At n m = Fin n → μML At m


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

----------------------------------------
-- Some kit for type-level arithmetic --
----------------------------------------

data Plus : ℕ → ℕ → ℕ → Set where
  idl : ∀ {n} → Plus zero n n
  sucl : ∀ {n m r} → Plus n m r → Plus (suc n) m (suc r)

idr : ∀ {n} → Plus n zero n
idr {zero} = idl
idr {suc n} = sucl idr

sucr : ∀ {a b a+b} → Plus a b a+b → Plus a (suc b) (suc a+b)
sucr idl = idl
sucr (sucl x) = sucl (sucr x)

split : ∀ {a b a+b} → Plus a b a+b → Fin a+b → Fin a ⊎ Fin b
split idl x = inj₂ x
split (sucl p) F.zero = inj₁ F.zero
split (sucl p) (F.suc x) = map F.suc id (split p x)

injectL : ∀ {n m n+m} → Plus n m n+m → Fin n → Fin n+m
injectL (sucl p) F.zero = F.zero
injectL (sucl p) (F.suc x) = F.suc (injectL p x)

thin : ∀ {At n m n+m} → Plus n m n+m → μML At n → μML At n+m
thin p (var x) = var (injectL p x)
thin p (μML₀ op) = μML₀ op
thin p (μML₁ op ϕ) = μML₁ op (thin p ϕ)
thin p (μML₂ op ϕl ϕr) = μML₂ op (thin p ϕl) (thin p ϕr)
thin p (μMLη op ϕ) = μMLη op (thin (sucl p) ϕ)

plus : ∀ n m → Plus n m (n + m)
plus zero m = idl
plus (suc n) m = sucl (plus n m)


-- Properties --

Plus-irrelevant : ∀ {a b a+b} → Irrelevant (Plus a b a+b)
Plus-irrelevant idl idl = refl
Plus-irrelevant (sucl p) (sucl q) = cong sucl (Plus-irrelevant p q)

Plus-comm : ∀ {a b a+b} → Plus a b a+b → Plus b a a+b
Plus-comm idl = idr
Plus-comm (sucl x) = sucr (Plus-comm x)

Plus-to-eq : ∀ {a b a+b} → Plus a b a+b → a + b ≡ a+b
Plus-to-eq idl = refl
Plus-to-eq (sucl x) = cong suc (Plus-to-eq x)

injectL-id : ∀ {n} (p : Plus n 0 n) (x : Fin n) → x ≡ injectL p x
injectL-id (sucl p) F.zero = refl
injectL-id (sucl p) (F.suc x) = cong F.suc (injectL-id p x)

thin-idl : ∀ {At n} (p : Plus n 0 n) (ϕ : μML At n) → ϕ ≡ thin p ϕ
thin-idl p (var x) = cong var (injectL-id p x)
thin-idl p (μML₀ op) = refl
thin-idl p (μML₁ op ϕ) = cong (μML₁ op) (thin-idl p ϕ)
thin-idl p (μML₂ op ϕl ϕr) = cong₂ (μML₂ op) (thin-idl p ϕl) (thin-idl p ϕr)
thin-idl p (μMLη op ϕ) = cong (μMLη op) (thin-idl (sucl p) ϕ)

injectL-sucl : ∀ {n} (p : Plus n 0 n) (x : Fin (suc n)) → injectL (sucl p) x ≡ x
injectL-sucl p F.zero = refl
injectL-sucl p (F.suc x) = cong F.suc (sym (injectL-id p x))

thin-sucl : ∀ {At n} (p : Plus n 0 n) (ϕ : μML At (suc n)) → thin (sucl p) ϕ ≡ ϕ
thin-sucl p (var x) = cong var (injectL-sucl p x)
thin-sucl p (μML₀ op) = refl
thin-sucl p (μML₁ op ϕ) = cong (μML₁ op) (thin-sucl p ϕ)
thin-sucl p (μML₂ op ϕl ϕr) = cong₂ (μML₂ op) (thin-sucl p ϕl) (thin-sucl p ϕr)
thin-sucl p (μMLη op ϕ) = cong (μMLη op) (thin-sucl (sucl p) ϕ)

split-idr : ∀ {n} → (p : Plus n 0 n) → (x : Fin n) → split p x ≡ inj₁ x
split-idr (sucl p) F.zero = refl
split-idr (sucl p) (F.suc x) rewrite split-idr p x = refl

-- If we know that the left is nonzero, then the first var definitely gets mapped there
split-zero : ∀ {a b a+b} → (p : Plus (suc a) b (suc a+b)) → split p F.zero ≡ inj₁ F.zero
split-zero (sucl p) = refl

ext-injectL : ∀ {a b a+b} → (p : Plus a b a+b) (q : Plus (suc a) b (suc a+b) )
            → ext (injectL p) ≗ injectL q
ext-injectL p (sucl q) F.zero = refl
ext-injectL p (sucl q) (F.suc x) = cong (λ a → F.suc (injectL a x)) (Plus-irrelevant p q)

-------------------------
-- Single Substitution --
-------------------------

-- Single substitution: sub in ϕ at 0, and decrement all other variables by 1
sub₀ : ∀ {At n} → μML At n → Subst At (suc n) n
sub₀ ϕ F.zero = ϕ -- at 0 we substitute
sub₀ ϕ (F.suc x) = var x

-- Single substitutions at higher indices
sub-n : ∀ {At k n k+n} → Plus k n k+n → μML At n → Subst At (suc k+n) k+n
sub-n idl = sub₀
sub-n (sucl p) = exts ∘ sub-n p

-- Single substitution at higher indices, with type-level arithmetic
sub-n' : ∀ {At n} k → μML At n → Subst At ((suc k) + n) (k + n)
sub-n' zero = sub₀
sub-n' (suc k) = exts ∘ sub-n' k

-- Single substitution is a special case of parallel substitution
_[_] : ∀ {At n} → μML At (suc n) → μML At n → μML At n
ϕ [ δ ] = sub (sub₀ δ) ϕ

-- Single substitution at index 1
_[_]' : ∀ {At n} → μML At (2+ n) → μML At n → μML At (suc n)
ϕ [ δ ]' = sub (sub-n (sucl idl) δ) ϕ

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

rename-cong : ∀ {At i j} {ρ ρ' : Rename i j}
            → ρ ≗ ρ'
            → rename {At} ρ ≗ rename ρ'
rename-cong eq (var x) = cong var (eq x)
rename-cong eq (μML₀ op) = refl
rename-cong eq (μML₁ op ϕ) = cong (μML₁ op) (rename-cong eq ϕ)
rename-cong eq (μML₂ op ϕl ϕr) = cong₂ (μML₂ op) (rename-cong eq ϕl) (rename-cong eq ϕr)
rename-cong eq (μMLη op ϕ) = cong (μMLη op) (rename-cong (ext-eq eq) ϕ)

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


----------------------------------
-- Other Properties of Renaming --
----------------------------------

rename-preserves-fp : ∀ {At n m} → {ρ : Rename n m} → (ϕ : μML At n) → {{_ : IsFP ϕ}} → IsFP (rename ρ ϕ)
rename-preserves-fp (μMLη op ϕ) = fp

rename-id : ∀ {At n} → (ϕ : μML At n) → rename id ϕ ≡ ϕ
rename-id (var x) = refl
rename-id (μML₀ op) = refl
rename-id (μML₁ op ϕ) = cong (μML₁ op) (rename-id ϕ)
rename-id (μML₂ op ϕl ϕr) = cong₂ (μML₂ op) (rename-id ϕl) (rename-id ϕr)
rename-id (μMLη op ϕ) = cong (μMLη op) (trans (rename-cong ext-id ϕ) (rename-id ϕ))


--------------------------------------
-- Other Properties of Substitution --
--     (and related machinery)      --
--------------------------------------


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


