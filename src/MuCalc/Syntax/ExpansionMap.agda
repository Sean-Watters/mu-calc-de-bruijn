{-# OPTIONS --allow-unsolved-metas #-}
module MuCalc.Syntax.ExpansionMap where

open import Function

open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin as F using (Fin) renaming (_ℕ-ℕ_ to _-_)
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Irrelevant; Dec; yes; no)


open import MuCalc.Base
open import MuCalc.Syntax.Subformula
open import MuCalc.Syntax.Substitution

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


-- The expansion map, by induction on the formula.
expand' : ∀ {At n b n+b} → Plus n b n+b → Scope At n → μML At n+b → μML At b
expand-var : ∀ {At n b} → (Γ : Scope At n) → (x : Fin n ⊎ Fin b) → μML At b

expand' p Γ (μML₀ op) = μML₀ op
expand' p Γ (μML₁ op ϕ) = μML₁ op (expand' p Γ ϕ)
expand' p Γ (μML₂ op ϕl ϕr) = μML₂ op (expand' p Γ ϕl) (expand' p Γ ϕr)
expand' {At} {n} p Γ (μMLη op ϕ) = μMLη op (expand' (sucr p) Γ ϕ)
expand' {n = n} p Γ (var x) = expand-var Γ (split p x)

expand-var Γ (inj₂ x) = var x -- bound vars are left alone
expand-var {n = suc n} {b} (ϕ ,- Γ) (inj₁ F.zero)
  = expand' {n = n} {b} {n + b} (plus n b) Γ (thin (plus n b) ϕ) -- free var; lookup and expand
expand-var (ϕ ,- Γ) (inj₁ (F.suc x)) = expand-var Γ (inj₁ x)

expand : ∀ {At n} → Scope At n → μML At n → μML At 0
expand Γ ϕ = expand' idr Γ (thin idr ϕ)



-----------------------------
-- Properties of Expansion --
-----------------------------

Plus-irrelevant : ∀ {a b a+b} → Irrelevant (Plus a b a+b)
Plus-irrelevant idl idl = refl
Plus-irrelevant (sucl p) (sucl q) = cong sucl (Plus-irrelevant p q)


expand'-thin : ∀ {At n n' n''} (Γ : Scope At n) (ϕ : μML At (suc n))
             → (p : Plus n 0 n') (q : Plus n 0 n'')
             → n ≡ n' → n ≡ n''
             → expand' (sucr p) Γ (thin (sucl p) ϕ) ≡ expand' (sucr q) Γ (thin (sucl q) ϕ)
expand'-thin Γ ϕ p q refl refl rewrite Plus-irrelevant p q = refl

---

injectL-id : ∀ {n} (p : Plus n 0 n) (x : Fin n) → x ≡ injectL p x
injectL-id (sucl p) F.zero = refl
injectL-id (sucl p) (F.suc x) = cong F.suc (injectL-id p x)

thin-idl : ∀ {At n} (p : Plus n 0 n) (ϕ : μML At n) → ϕ ≡ thin p ϕ
thin-idl p (var x) = cong var (injectL-id p x)
thin-idl p (μML₀ op) = refl
thin-idl p (μML₁ op ϕ) = cong (μML₁ op) (thin-idl p ϕ)
thin-idl p (μML₂ op ϕl ϕr) = cong₂ (μML₂ op) (thin-idl p ϕl) (thin-idl p ϕr)
thin-idl p (μMLη op ϕ) = cong (μMLη op) (thin-idl (sucl p) ϕ)

expand-empty' : ∀ {At b} → (p : Plus 0 b b) → (ϕ : μML At b) → ϕ ≡ expand' p [] ϕ
expand-empty' p (μML₀ op) = refl
expand-empty' p (μML₁ op ϕ) = cong (μML₁ op) (expand-empty' p ϕ)
expand-empty' p (μML₂ op ϕl ϕr) = cong₂ (μML₂ op) (expand-empty' p ϕl) (expand-empty' p ϕr)
expand-empty' p (μMLη op ϕ) = cong (μMLη op) (expand-empty' (sucr p) ϕ)
expand-empty' idl (var x) = refl

expand-empty : ∀ {At} (ϕ : μML At 0) → ϕ ≡ expand [] ϕ
expand-empty ϕ = trans (expand-empty' idl ϕ) (cong (expand' idl []) {ϕ} {thin idl ϕ} (thin-idl idl ϕ))

---

expandvar-extend : ∀ {At n m} (Γ : Scope At n) (ϕ : μML At n)
                 → (x : Fin n ⊎ Fin m)
                 → expand-var (ϕ ,- Γ) (map F.suc id x) ≡ expand-var Γ x
expandvar-extend _ _ (inj₁ x) = refl
expandvar-extend _ _ (inj₂ y) = refl

injectL-sucl : ∀ {n} (p : Plus n 0 n) (x : Fin (suc n)) → injectL (sucl p) x ≡ x
injectL-sucl p F.zero = refl
injectL-sucl p (F.suc x) = cong F.suc (sym (injectL-id p x))

thin-sucl : ∀ {At n} (p : Plus n 0 n) (ϕ : μML At (suc n)) → thin (sucl p) ϕ ≡ ϕ
thin-sucl p (var x) = cong var (injectL-sucl p x)
thin-sucl p (μML₀ op) = refl
thin-sucl p (μML₁ op ϕ) = cong (μML₁ op) (thin-sucl p ϕ)
thin-sucl p (μML₂ op ϕl ϕr) = cong₂ (μML₂ op) (thin-sucl p ϕl) (thin-sucl p ϕr)
thin-sucl p (μMLη op ϕ) = cong (μMLη op) (thin-sucl (sucl p) ϕ)

_?=_ : ∀ {n m} → (x y : Fin n ⊎ Fin m) → Dec (x ≡ y)
inj₁ x ?= inj₂ y = no (λ ())
inj₂ y ?= inj₁ x = no (λ ())
inj₁ x ?= inj₁ x' with x F.≟ x'
... | yes p = yes (cong inj₁ p)
... | no ¬p = no (λ {refl → ¬p refl})
inj₂ y ?= inj₂ y' with y F.≟ y'
... | yes p = yes (cong inj₂ p)
... | no ¬p = no (λ {refl → ¬p refl})

sub-expand : ∀ {At n b n+b} (Γ : Scope At n) (ϕ : μML At n+b)
           → (p : Plus n (suc b) n+b) (q : Plus (suc n) b n+b)
           → {ψ : μML At n} {r : n+b ≥ n} → SforNE r ϕ ψ
           → (σ : Subst At (suc b) b)
           -- todo - what invarients do we need for σ?
           -- Needs to only substitute 1 var for ψ and everything else for a rescoping?
           → sub σ (expand' p Γ ϕ) ≡ expand' q (ψ ,- Γ) ϕ

sub-expand-var : ∀ {At n b n+b} (Γ : Scope At n) 
               → (p : Plus n (suc b) n+b) (q : Plus (suc n) b n+b)
               → (x : Fin n ⊎ Fin (suc b)) (x' : Fin (suc n) ⊎ Fin b)
               → {ψ : μML At n}
               → (σ : Subst At (suc b) b) → IsSingleSub σ
               → sub σ (expand-var Γ x) ≡ expand-var (ψ ,- Γ) x'

sub-expand Γ (var x) p q sf σ = {!sub-expand-var!}
sub-expand Γ (μML₀ op) p q sf σ = refl
sub-expand Γ (μML₁ op ϕ) p q {r = r} sf σ = cong (μML₁ op) (sub-expand Γ ϕ p q (cons ≤-refl _ r (down op) sf) σ )
sub-expand Γ (μML₂ op ϕl ϕr) p q {r = r} sf σ = cong₂ (μML₂ op) (sub-expand Γ ϕl p q (cons ≤-refl _ r (left op) sf) σ) (sub-expand Γ ϕr p q (cons ≤-refl _ r (right op) sf) σ)
sub-expand Γ (μMLη op ϕ) p q {r = r} sf σ = cong (μMLη op) (sub-expand Γ ϕ (sucr p) (sucr q) (cons (m≤n⇒m≤1+n ≤-refl) _ (m≤n⇒m≤1+n r) (under op) sf) (exts σ) )

sub-expand-var Γ p q x x' σ (aye y refl ifne) = {!todo -graphify expand-var!}


unfold-expand : ∀ {At n} op (Γ : Scope At n) (ϕ : μML At (suc n)) (p : Plus n 1 (suc n)) (q : Plus (suc n) 0 (suc n))
              → unfold (μMLη op (expand' p Γ ϕ)) ≡ expand' q (μMLη op ϕ ,- Γ) ϕ
unfold-expand {At} {n} op Γ ϕ p q = sub-expand Γ ϕ p q (dsf (m≤n⇒m≤1+n ≤-refl) (under op)) (sub₀ (μMLη op (expand' p Γ ϕ)))

