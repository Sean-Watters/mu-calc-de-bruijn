{-# OPTIONS --allow-unsolved-metas #-}
module MuCalc.DeBruijn.ExpansionMap where

open import Function

open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin as F using (Fin) renaming (_ℕ-ℕ_ to _-_)
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Irrelevant)


open import MuCalc.DeBruijn.Base

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

unfold-expand : ∀ {At n} op (Γ : Scope At n) (ϕ : μML At (suc n)) (p : Plus n 1 (suc n)) (q : Plus (suc n) 0 (suc n))
              → unfold (μMLη op (expand' p Γ ϕ)) ≡ expand' q (μMLη op ϕ ,- Γ) ϕ
unfold-expand a Γ (var x) p q = {!!}
unfold-expand a Γ (μML₀ b) p q = refl
unfold-expand a Γ (μML₁ b ϕ) p q = cong (μML₁ b) {!unfold-expand a Γ ϕ p q!}
unfold-expand a Γ (μML₂ b ϕl ϕr) p q = cong₂ (μML₂ b) {!!} {!!}
unfold-expand a Γ (μMLη b ϕ) p q = cong (μMLη b) {!!}
