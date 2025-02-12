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

-- The expansion map, by induction on the formula.
-- Ran into trouble trying to prove the 2nd characteristic equation, but this bit of
-- wisdom from Guillaume helped - use pre-thinned scopes and thin every time you traverse a
-- binder, rather than telescopes with the thinning at the leaves.
-- Unfortunately, this means the termination checker can't see that Γ is getting smaller any more,
-- through the V.map. So we need some WFI.
expand' : ∀ {At n b n+b} → Plus n b n+b → (Γ : Vec (μML At n+b) n) → μML At n+b → μML At b
expand-var : ∀ {At n b n+b} → Plus n b n+b → (Γ : Vec (μML At n+b) n) → (x : Fin n ⊎ Fin b) → μML At b
expand-var-lookup : ∀ {At n b n+b} → {p : Plus n b n+b} → (Γ : Vec (μML At n+b) n)
                  → {x : Fin n} {x' : Fin n+b} → IsThinnedVar p x x' → μML At b

expand' p Γ (μML₀ op) = μML₀ op
expand' p Γ (μML₁ op ϕ) = μML₁ op (expand' p Γ ϕ)
expand' p Γ (μML₂ op ϕl ϕr) = μML₂ op (expand' p Γ ϕl) (expand' p Γ ϕr)
expand' p Γ (μMLη op ϕ) = μMLη op (expand' (sucr p) (V.map (thin (sucr idr)) Γ) ϕ)
expand' p Γ (var x) = expand-var p Γ (split p x)

expand-var p Γ (inj₁ x) = expand-var-lookup Γ (injectL-thins p x)
expand-var p Γ (inj₂ x) = var x -- bound vars are left alone

expand-var-lookup {At} {suc n} {b} {suc n+b} {sucl p} (ϕ ∷ Γ) {x} {x'} zero = expand' {!p -- but why :(!} Γ ϕ
expand-var-lookup {At} {suc n} {b} {suc n+b} {sucl p} (ϕ ∷ Γ) {x} {x'} (suc xth) = expand-var-lookup Γ {!!}

expand : ∀ {At n} → Scope At n → μML At n → μML At 0
expand Γ ϕ = expand' idr {!!} (thin idr ϕ)

{-
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

-- Unit test for expand --

phi3 : μML ℕ 3
phi3 = (var F.zero ∧ var (F.suc F.zero)) ∧ var (F.suc (F.suc F.zero))

phi2 : μML ℕ 2
phi2 = μ (■ phi3)

phi1 : μML ℕ 1
phi1 = ν (◆ phi2)

phi0 : μML ℕ 0
phi0 = μ (◆ phi1)

test : expand (phi2 ,- phi1 ,- phi0 ,- []) phi3 ≡ expand (phi1 ,- phi0 ,- []) (phi3 [ phi2 ])
test = refl

-----------------------------
-- Properties of Expansion --
-----------------------------

Plus-irrelevant : ∀ {a b a+b} → Irrelevant (Plus a b a+b)
Plus-irrelevant idl idl = refl
Plus-irrelevant (sucl p) (sucl q) = cong sucl (Plus-irrelevant p q)

Plus-to-eq : ∀ {a b a+b} → Plus a b a+b → a + b ≡ a+b
Plus-to-eq idl = refl
Plus-to-eq (sucl x) = cong suc (Plus-to-eq x)

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


expand-cons' : ∀ {At n b n+b} (p : Plus n b n+b) (Γ : Scope At n) (ψ : μML At n) (ϕ : μML At (suc n+b))
             → expand' (sucl p) (ψ ,- Γ) ϕ ≡ expand' p Γ (ϕ [ thin p ψ ])
expand-cons' p Γ ψ (μML₀ op) = refl
expand-cons' p Γ ψ (μML₁ op ϕ) = cong (μML₁ op) (expand-cons' p Γ ψ ϕ)
expand-cons' p Γ ψ (μML₂ op ϕl ϕr) = cong₂ (μML₂ op) (expand-cons' p Γ ψ ϕl) (expand-cons' p Γ ψ ϕr)
expand-cons' p Γ ψ (μMLη op ϕ) = cong (μMLη op) (trans (expand-cons' (sucr p) Γ ψ ϕ) {!!} )
expand-cons' p Γ ψ (var x) = {!!}

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
