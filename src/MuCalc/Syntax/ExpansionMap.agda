{-# OPTIONS --allow-unsolved-metas #-}
module MuCalc.Syntax.ExpansionMap where

open import Function

open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin as F using (Fin) renaming (_ℕ-ℕ_ to _-_)
open import Data.Sum
open import Data.Vec as V using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary using (Irrelevant; Dec; yes; no)


open import MuCalc.Base
open import MuCalc.Syntax.Subformula
open import MuCalc.Syntax.Substitution

{-
data IsThinnedVar : {n m n+m : ℕ} (p : Plus n m n+m) → Fin n → Fin n+m → Set where
  zero : ∀ {n m n+m} {p : Plus n m n+m} → IsThinnedVar (sucl p) F.zero F.zero
  suc  : ∀ {n m n+m} {p : Plus n m n+m} {x : Fin n} {y : Fin n+m} → IsThinnedVar p x y → IsThinnedVar (sucl p) (F.suc x) (F.suc y)

data IsThinned {At : Set} {n m n+m : ℕ} (p : Plus n m n+m) : μML At n → μML At n+m → Set where
  var : ∀ {x y} → IsThinnedVar p x y → IsThinned p (var x) (var y)
  μML₀ : ∀ op → IsThinned p (μML₀ op) (μML₀ op)
  μML₁ : ∀ op {ϕ : μML At n} {ϕ' : μML At n+m} → IsThinned p ϕ ϕ' → IsThinned p (μML₁ op ϕ) (μML₁ op ϕ')
  μML₂ : ∀ op {ϕl ϕr : μML At n} {ϕl' ϕr' : μML At n+m} → IsThinned p ϕl ϕl' → IsThinned p ϕr ϕr' → IsThinned p (μML₂ op ϕl ϕr) (μML₂ op ϕl' ϕr')
  μMLη : ∀ op {ϕ : μML At n} {ϕ' : μML At n+m} → IsThinned p ϕ ϕ' → IsThinned p (μML₁ op ϕ) (μML₁ op ϕ')

data Join : {n m n+m : ℕ} → (Fin n ⊎ Fin m) → Fin n+m → Set where
  lz : ∀ {n m n+m} → Join {suc n} {m} {suc n+m} (inj₁ F.zero) (F.zero)
  ls : ∀ {n m n+m} {x : Fin n} {y : Fin n+m} → Join {m = m} (inj₁ x) y → Join {m = m} (inj₁ (F.suc x)) (F.suc y)
  rz : ∀ {n m n+m} → Join {n} {suc m} {suc n+m} (inj₂ F.zero) (F.fromℕ n+m)
  rs : ∀ {n m n+m} {x : Fin m} {y : Fin n+m} → Join {n} (inj₂ x) y → Join {n} (inj₂ (F.suc x)) (F.suc y)

injectL-thins : ∀ {n m n+m} → (p : Plus n m n+m) → (x : Fin n) → IsThinnedVar p x (injectL p x)
injectL-thins (sucl p) F.zero = zero
injectL-thins (sucl p) (F.suc x) = suc (injectL-thins p x)
-}


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

expand'-cong : ∀ {At n m n+m u v u+v} (p : Plus n m n+m) (q : Plus u v u+v)
             → (eq1 : n ≡ u) (eq2 : m ≡ v) (eq3 : n+m ≡ u+v)
             → (Γ : Scope At n) (Δ : Scope At u)
             → subst (Scope At) eq1 Γ ≡ Δ
             → (ϕ : μML At n+m) (ψ : μML At u+v)
             → subst (μML At) eq3 ϕ ≡ ψ
             → subst (μML At) eq2 (expand' p Γ ϕ) ≡ expand' q Δ ψ
expand'-cong p q refl refl refl Γ Δ refl ϕ ψ refl rewrite Plus-irrelevant p q = refl


-- expand'-lem : ∀ {At n m n+m u v u+v} (p : Plus n m n+m) (q : Plus u v u+v)
--             → (eq1 : n+m ≡ u+v)
--             → (Γ : Scope At n)
--             → (ϕ : μML At n+m) (ψ : μML At u+v)
--             → subst (μML At) eq1 ϕ ≡ ψ
--             → {! expand' p Γ ϕ !} ≡ expand' q Γ ψ
-- expand'-lem = ?


----------------------------------------------
-- The Characteristic Equations of `expand` --
----------------------------------------------

{-

The "morally correct" definition of the expansion map is:

```
expand : ∀ {At n} → Scope At n → μML At n → μML At 0
expand []       ϕ = ϕ
expand (ψ ,- Γ) ϕ = expand Γ (ϕ [ ψ ])
```

However, this made proofs harder, because everything else computes by induction on the
formula, not the scope. So we moved to the above more complex definition which does proceed by
induction on the formula.

We now prove that the equations of the original definition hold for the new one as theorems.

-}


expand-nil' : ∀ {At b} → (p : Plus 0 b b) → (ϕ : μML At b) → ϕ ≡ expand' p [] ϕ
expand-nil' p (μML₀ op) = refl
expand-nil' p (μML₁ op ϕ) = cong (μML₁ op) (expand-nil' p ϕ)
expand-nil' p (μML₂ op ϕl ϕr) = cong₂ (μML₂ op) (expand-nil' p ϕl) (expand-nil' p ϕr)
expand-nil' p (μMLη op ϕ) = cong (μMLη op) (expand-nil' (sucr p) ϕ)
expand-nil' idl (var x) = refl

expand-nil : ∀ {At} (ϕ : μML At 0) → ϕ ≡ expand [] ϕ
expand-nil ϕ = trans (expand-nil' idl ϕ) (cong (expand' idl []) {ϕ} {thin idl ϕ} (thin-idl idl ϕ))

expand-var-extend : ∀ {At n m} (Γ : Scope At n) (ϕ : μML At n)
                 → (x : Fin n ⊎ Fin m)
                 → expand-var (ϕ ,- Γ) (map F.suc id x) ≡ expand-var Γ x
expand-var-extend _ _ (inj₁ x) = refl
expand-var-extend _ _ (inj₂ y) = refl

expand-cons' : ∀ {At n b n+b} (p : Plus n b n+b) (q : Plus b n n+b) (Γ : Scope At n) (ψ : μML At n) (ϕ : μML At (suc n+b))
             → expand' (sucl p) (ψ ,- Γ) ϕ ≡ expand' p Γ (sub (sub-n q ψ) ϕ)
expand-cons-var : ∀ {At n b n+b} (p : Plus n b n+b) (q : Plus b n n+b) (Γ : Scope At n) (ψ : μML At n) (x : Fin (suc n+b))
                → expand-var (ψ ,- Γ) (split (sucl p) x) ≡ expand' p Γ (sub-n q ψ x)


expand-cons' p q Γ ψ (μML₀ op) = refl
expand-cons' p q Γ ψ (μML₁ op ϕ) = cong (μML₁ op) (expand-cons' p q Γ ψ ϕ)
expand-cons' p q Γ ψ (μML₂ op ϕl ϕr) = cong₂ (μML₂ op) (expand-cons' p q Γ ψ ϕl) (expand-cons' p q Γ ψ ϕr)
expand-cons' p q Γ ψ (μMLη op ϕ) = cong (μMLη op) (expand-cons' (sucr p) (sucl q) Γ ψ ϕ)
expand-cons' p q Γ ψ (var x) = expand-cons-var p q Γ ψ x

expand-cons-var {At} {n} {0} {n} p idl Γ ψ F.zero
  = expand'-cong (plus n 0) p refl refl (+-identityʳ n) Γ Γ refl (thin (plus n 0) ψ) ψ (trans {!Plus-irrelevant (plus n 0)!} (sym $ thin-idl p ψ))
expand-cons-var {At} {n} {0} {n} p idl Γ ψ (F.suc x) = expand-var-extend Γ ψ (split p x)
expand-cons-var {At} {n} {suc b} {suc n+b} p (sucl q) Γ ψ F.zero = {!!}
expand-cons-var {At} {n} {suc b} {suc n+b} p (sucl q) Γ ψ (F.suc x) =
  begin
    expand-var (ψ ,- Γ) (split (sucl p) (F.suc x))
  ≡⟨ expand-var-extend Γ ψ (split p x) ⟩
    expand-var Γ (split p x)
  ≡⟨ {!expand-cons-var  !} ⟩
    expand' p Γ (sub-n (sucl q) ψ (F.suc x))
  ∎ where open ≡-Reasoning

  -- begin
  --   expand' (plus n b) Γ (thin (plus n b) ψ)
  -- ≡⟨ expand'-cong (plus n b) p refl refl (Plus-to-eq p) Γ Γ refl (thin (plus n b) ψ) (thin p ψ) (unsubst ψ p (plus n b) (Plus-to-eq p)) ⟩
  --   expand' p Γ (thin p ψ)
  -- ≡⟨ {!cong (expand' p Γ)!} ⟩
  --   expand' p Γ (sub-n q ψ F.zero)
  -- ∎ where
  --   open ≡-Reasoning
  --   unsubst : ∀ {At n b n+b} (ψ : μML At n) (p : Plus n b n+b) (q : Plus n b (n + b))
  --           → (eq : n + b ≡ n+b)
  --           → subst (μML At) eq (thin q ψ) ≡ thin p ψ
  --   unsubst ψ p q refl rewrite Plus-irrelevant p q = refl

-- expand-cons-var p q Γ ψ (F.suc x) = {!!}

{-

expand-cons : ∀ {At n} (Γ : Scope At n) (ψ : μML At n) (ϕ : μML At (suc n))
            → expand (ψ ,- Γ) ϕ ≡ expand Γ (ϕ [ ψ ])
expand-cons Γ ψ ϕ =
  begin
    expand' (sucl idr) (ψ ,- Γ) (thin (sucl idr) ϕ)
  ≡⟨ cong (expand' (sucl idr) (ψ ,- Γ)) (sym $ thin-idl (sucl idr) ϕ) ⟩
    expand' (sucl idr) (ψ ,- Γ) ϕ
  ≡⟨ expand-cons' idr Γ ψ ϕ ⟩
    expand' idr Γ (ϕ [ thin idr ψ ])
  ≡⟨ cong (λ a → expand' idr Γ (ϕ [ a ])) (sym $ thin-idl idr ψ) ⟩
    expand' idr Γ (ϕ [ ψ ])
  ≡⟨ cong (expand' idr Γ) (thin-idl idr (ϕ [ ψ ])) ⟩
    expand' idr Γ (thin idr (sub (sub₀ ψ) ϕ))
  ∎ where open ≡-Reasoning

----------------------------------
-- Other Properties of `expand` --
----------------------------------


_?=_ : ∀ {n m} → (x y : Fin n ⊎ Fin m) → Dec (x ≡ y)
inj₁ x ?= inj₂ y = no (λ ())
inj₂ y ?= inj₁ x = no (λ ())
inj₁ x ?= inj₁ x' with x F.≟ x'
... | yes p = yes (cong inj₁ p)
... | no ¬p = no (λ {refl → ¬p refl})
inj₂ y ?= inj₂ y' with y F.≟ y'
... | yes p = yes (cong inj₂ p)
... | no ¬p = no (λ {refl → ¬p refl})



expand-sub : ∀ {At n} op (Γ : Scope At n) (ϕ : μML At (suc n)) (p : Plus n 1 (suc n))
           → (expand' p Γ ϕ) [ μMLη op (expand' p Γ ϕ) ] ≡ expand Γ (ϕ [ μMLη op ϕ ])
expand-sub op [] ϕ p =
  let lem1 = expand-nil' p ϕ
      lem2 = expand-nil (ϕ [ μMLη op ϕ ])
  in begin
    (expand' p [] ϕ) [ μMLη op (expand' p [] ϕ) ]
  ≡⟨ cong₂ (λ a b → a [ μMLη op b ]) (sym lem1) (sym lem1) ⟩
    (ϕ [ μMLη op ϕ ])
  ≡⟨ lem2 ⟩
    expand [] (ϕ [ μMLη op ϕ ])
  ∎ where open ≡-Reasoning
expand-sub op (ψ ,- Γ) ϕ (sucl p) =
  let lem1 = expand-cons' p Γ ψ ϕ
      lem2 = expand-cons Γ ψ (ϕ [ μMLη op ϕ ])
  in begin
    (expand' _ (ψ ,- Γ) ϕ) [ μMLη op (expand' _ (ψ ,- Γ) ϕ) ]
  ≡⟨ cong (λ a → a [ μMLη op a ]) lem1 ⟩
    (expand' _ Γ (ϕ [ thin p ψ ])) [ μMLη op (expand' _ Γ (ϕ [ thin p ψ ])) ]
  ≡⟨ expand-sub op Γ (ϕ [ thin p ψ ]) p  ⟩
    expand Γ ((ϕ [ thin p ψ ]) [ μMLη op (ϕ [ thin p ψ ]) ])
  ≡⟨ {!!} ⟩
    expand Γ ((ϕ [ ψ ]') [ μMLη op ϕ [ ψ ] ])
  ≡⟨ cong (expand Γ) (sym $ substitution-lemma ϕ (μMLη op ϕ) ψ) ⟩
    expand Γ ((ϕ [ μMLη op ϕ ]) [ ψ ])
  ≡⟨ sym lem2 ⟩
    expand (ψ ,- Γ) (ϕ [ μMLη op ϕ ])
  ∎ where open ≡-Reasoning

unfold-expand : ∀ {At n} op (Γ : Scope At n) (ϕ : μML At (suc n)) (p : Plus n 1 (suc n))
              → unfold (μMLη op (expand' p Γ ϕ)) ≡ expand (μMLη op ϕ ,- Γ) ϕ
unfold-expand {At} {n} op Γ ϕ p =
  begin
    (expand' p Γ ϕ) [ μMLη op (expand' p Γ ϕ) ]
  ≡⟨ expand-sub op Γ ϕ p ⟩
    expand Γ (ϕ [ μMLη op ϕ ])
  ≡⟨ (sym $ expand-cons Γ (μMLη op ϕ) ϕ) ⟩
    expand (μMLη op ϕ ,- Γ) ϕ
  ∎ where open ≡-Reasoning

-}
