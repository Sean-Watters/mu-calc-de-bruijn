{-# OPTIONS --rewriting #-}
module MuCalc.Syntax.ExpansionMap where

open import Function

open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin as F using (Fin) renaming (_ℕ-ℕ_ to _-_)
open import Data.Fin.Properties as F
open import Data.Fin.Renaming
open import Data.Thinning as Th hiding (id)
open import Data.Sum as S
open import Data.Product
open import Data.Vec as V using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary using (Irrelevant; Dec; yes; no)

open import MuCalc.Base
open import MuCalc.Syntax.Substitution

-------------------
-- Rewrite Rules --
-------------------

open import Rewrite.Plus

-- NB: Rewrite rules are directed, so these will only replace occurrences of the LHS.

---------------------------------
-- Definition of Expansion Map --
---------------------------------

expand : ∀ {At n b} → Scope At n → μML At (b + n) → μML At b
expand-var : ∀ {At n b} → (Γ : Scope At n) → (x : Fin b ⊎ Fin n) → μML At b

expand {b = b} Γ (var x) = expand-var Γ (F.splitAt b x )
expand Γ (μML₀ op) = μML₀ op
expand Γ (μML₁ op ϕ) = μML₁ op (expand Γ ϕ)
expand Γ (μML₂ op ϕl ϕr) = μML₂ op (expand Γ ϕl) (expand Γ ϕr)
expand {At} {n} {b} Γ (μMLη op ϕ) = μMLη op (expand Γ ϕ)

expand-var Γ (inj₁ x) = var x -- BVs are left alone
expand-var {n = suc n} {b = b} (ϕ ,- Γ) (inj₂ F.zero) = expand Γ (rename (b F.↑ʳ_) ϕ )
expand-var (ϕ ,- Γ) (inj₂ (F.suc y)) = expand-var Γ (inj₂ y)


------------
-- Lemmas --
------------

-- Requires rewriting `n + 0` for `n`, to type check
splitAt-idr : ∀ {n} (x : Fin (n + 0)) → inj₁ x ≡ F.splitAt n {0} x
splitAt-idr F.zero = refl
splitAt-idr (F.suc x) = cong (S.map₁ F.suc) (splitAt-idr x)


-------------------------------------
-- `expand` Commutes with Renaming --
-------------------------------------

expand-rename : ∀ {At b n}
              → (θ : Thin b (suc b)) -- generalisation of suc, ext suc, ext ext suc, etc
              → (Γ : Scope At n) (ϕ : μML At (b + n))
              → rename (embed θ) (expand Γ ϕ) ≡ expand Γ (rename (embed (θ ⊗ Th.id n)) ϕ)
expand-rename-var : ∀ {At b n}
                  → (θ : Thin b (suc b))
                  → (Γ : Scope At n) (x : Fin b ⊎ Fin n)
                  → rename (embed θ) (expand-var Γ x)
                  ≡ expand-var Γ (S.map₁ (embed θ) x)

expand-rename {b = b} {n} θ Γ (var x) =
  begin
    rename (embed θ) (expand Γ (var x))
  ≡⟨  expand-rename-var θ Γ (F.splitAt b x)  ⟩
    expand-var Γ (S.map₁ (embed θ) (F.splitAt b x))
  ≡⟨ cong (expand-var Γ) (splitAt-embed-⊗ θ x) ⟩
    expand-var Γ (F.splitAt (suc b) (embed (θ ⊗ Th.id n) x))
  ∎ where open ≡-Reasoning
expand-rename θ Γ (μML₀ op) = refl
expand-rename θ Γ (μML₁ op ϕ) = cong (μML₁ op) (expand-rename θ Γ ϕ)
expand-rename θ Γ (μML₂ op ϕl ϕr) = cong₂ (μML₂ op) (expand-rename θ Γ ϕl) (expand-rename θ Γ ϕr)
expand-rename {n = n} θ Γ (μMLη op ϕ) = cong (μMLη op) $
  begin
    rename (ext (embed θ)) (expand Γ ϕ)
  ≡⟨ rename-cong (ext∘embed θ) (expand Γ ϕ) ⟩
    rename (embed (inj θ)) (expand Γ ϕ)
  ≡⟨ expand-rename (inj θ) Γ ϕ ⟩
    expand Γ (rename (embed (inj θ ⊗ Th.id n)) ϕ)
  ≡⟨ cong (expand Γ) (rename-cong (ext∘embed (θ ⊗ Th.id n)) ϕ) ⟨
    expand Γ (rename (ext (embed (θ ⊗ Th.id n))) ϕ)
  ∎ where open ≡-Reasoning

expand-rename-var θ Γ (inj₁ x) = refl
expand-rename-var {b = b} {suc n} θ (ϕ ,- Γ) (inj₂ F.zero) =
  begin
    rename (embed θ) (expand-var (ϕ ,- Γ) (inj₂ F.zero))
  ≡⟨ expand-rename θ Γ (rename (b F.↑ʳ_) ϕ) ⟩
    expand Γ (rename (embed (θ ⊗ Th.id n)) (rename (b F.↑ʳ_) ϕ))
  ≡⟨ cong (expand Γ) (rename-fusion (λ x → trans (embed-↑ʳ θ (Th.id n) x) (cong (λ z → F.suc (b F.↑ʳ z)) (embed-id x))) ϕ) ⟩
    expand Γ (rename (F.suc ∘ (b F.↑ʳ_)) ϕ)
  ≡⟨⟩
    expand-var (ϕ ,- Γ) (S.map₁ (embed θ) (inj₂ F.zero))
  ∎ where open ≡-Reasoning
expand-rename-var θ (ϕ ,- Γ) (inj₂ (F.suc y)) = expand-rename-var θ Γ (inj₂ y)

-- The special case we actually care about. Couldn't prove it directly because going under binders
-- bumps `suc` up to `ext suc`.
expand-rename-suc : ∀ {At b n} → (Γ : Scope At n) (ϕ : μML At (b + n))
                  → rename F.suc (expand Γ ϕ) ≡ expand Γ (rename F.suc ϕ)
expand-rename-suc {b = b} {n} Γ ϕ =
  begin
    rename F.suc (expand Γ ϕ)
  ≡⟨ rename-cong embed-suc (expand Γ ϕ) ⟩
    rename (embed (inc b)) (expand Γ ϕ)
  ≡⟨ expand-rename (inc b) Γ ϕ ⟩
    expand Γ (rename (embed ((inc b) ⊗ Th.id n)) ϕ)
  ≡⟨ cong (expand Γ) (rename-cong lemma ϕ) ⟩
    expand Γ (rename F.suc ϕ)
  ∎ where
    open ≡-Reasoning
    lemma : embed ((inc b) ⊗ Th.id n) ≗ F.suc
    lemma x =
      begin
        F.suc (embed (Th.id b ⊗ Th.id n) x)
      ≡⟨ cong (λ z → F.suc (embed z x)) (⊗-id b) ⟩
        F.suc (embed (Th.id (b + n)) x)
      ≡⟨ embed-id (F.suc x) ⟩
        F.suc x
      ∎

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

expand-nil : ∀ {At b} → (ϕ : μML At b) → ϕ ≡ expand [] ϕ
expand-nil {b = b} (var x) = cong (expand-var []) (splitAt-idr x)
expand-nil (μML₀ op) = refl
expand-nil (μML₁ op ϕ) = cong (μML₁ op) (expand-nil ϕ)
expand-nil (μML₂ op ϕl ϕr) = cong₂ (μML₂ op) (expand-nil ϕl) (expand-nil ϕr)
expand-nil (μMLη op ϕ) = cong (μMLη op) (expand-nil ϕ)

-- Single substition and scope injection commute in the following way.
-- The type requires rewriting by +-suc
sub-n-↑ʳ : ∀ {At n} (k : ℕ) → (ϕ : μML At n) → (x : Fin (suc n))
         → rename (k F.↑ʳ_) (sub₀ ϕ x) ≡ sub-n' k ϕ (k F.↑ʳ x)
sub-n-↑ʳ zero ϕ x = rename-id _
sub-n-↑ʳ (suc k) ϕ x =
  begin
    rename (suc k F.↑ʳ_) (sub₀ ϕ x)
  ≡⟨ rename-fusion (λ _ → refl) (sub₀ ϕ x) ⟨
    rename F.suc (rename (F._↑ʳ_ k) (sub₀ ϕ x))
  ≡⟨ cong (rename F.suc) (sub-n-↑ʳ k ϕ x) ⟩
    sub-n' (suc k) ϕ (suc k F.↑ʳ x)
  ∎ where open ≡-Reasoning


expand-cons' : ∀ {At b n} (Γ : Scope At n) (ψ : μML At n)
             → (ϕ : μML At ((suc b) + n))
             → expand (ψ ,- Γ) ϕ ≡ expand Γ (sub (sub-n' b ψ) ϕ)
expand-cons'-var : ∀ {At b n} (Γ : Scope At n) (ψ : μML At n)
                → (x : Fin b ⊎ Fin (suc n)) (x' : Fin (b + (suc n)))
                → x' ≡ F.join b (suc n) x
                → expand-var (ψ ,- Γ) x ≡ expand Γ (sub-n' b ψ x')

expand-cons' {b = b} {n = n} Γ ψ (var x) = expand-cons'-var Γ ψ (F.splitAt b x) x (sym $ F.join-splitAt b (suc n) x )
expand-cons' Γ ψ (μML₀ op) = refl
expand-cons' Γ ψ (μML₁ op ϕ) = cong (μML₁ op) (expand-cons' Γ ψ ϕ)
expand-cons' Γ ψ (μML₂ op ϕl ϕr) = cong₂ (μML₂ op) (expand-cons' Γ ψ ϕl) (expand-cons' Γ ψ ϕr)
expand-cons' Γ ψ (μMLη op ϕ) = cong (μMLη op) (expand-cons' Γ ψ ϕ)

expand-cons'-var {At} {b} {n} Γ ψ (inj₁ x) x' refl = lem Γ ψ x where
  lem : ∀ {At b n} (Γ : Scope At n) (ψ : μML At n) (x : Fin b)
      → var x ≡ expand Γ (sub-n' b ψ (x F.↑ˡ (suc n)))
  lem Γ ψ F.zero = refl
  lem {b = suc b} {n = n} Γ ψ (F.suc x) =
    begin
      var (F.suc x)
    ≡⟨ cong (rename F.suc) (lem Γ ψ x) ⟩
      rename F.suc (expand Γ (sub-n' _ ψ (x F.↑ˡ suc n)))
    ≡⟨  expand-rename-suc Γ (sub-n' b ψ (x F.↑ˡ suc n)) ⟩
      expand Γ (sub-n' (suc b) ψ (F.suc x F.↑ˡ suc n))
    ∎ where open ≡-Reasoning
expand-cons'-var Γ ψ (inj₂ y) x' refl = lem1 Γ ψ y  where
  lem2 : ∀ {At b n} → (Γ : Scope At n) (ψ : μML At n) (y : Fin (suc n))
       → expand-var (ψ ,- Γ) (inj₂ y) ≡ expand Γ (rename (F._↑ʳ_ b) (sub₀ ψ y))
  lem2 Γ ψ F.zero = refl
  lem2 {b = b} Γ ψ (F.suc y) = sym $ cong (expand-var Γ) (splitAt-↑ʳ b _ y)

  lem1 : ∀ {At b n} → (Γ : Scope At n) (ψ : μML At n) (y : Fin (suc n))
      → expand-var (ψ ,- Γ) (inj₂ y) ≡ expand Γ (sub-n' b ψ (b F.↑ʳ y))
  lem1 {b = b} Γ ψ y = trans (lem2 Γ ψ y) (cong (expand Γ) (sub-n-↑ʳ b ψ y)) -- idea: we're only substituting an `n` variable, so the `b` doesnt matter


-- When b=0, we get the special case for single substution, which is the characteristic equation we want.
expand-cons : ∀ {At n} (Γ : Scope At n) (ψ : μML At n) (ϕ : μML At (suc n))
            → expand (ψ ,- Γ) ϕ ≡ expand Γ (ϕ [ ψ ])
expand-cons = expand-cons'


-----------------------------------------
-- `expand` Commutes with Substitution --
-----------------------------------------


sub-expand : ∀ {At n} op (Γ : Scope At n) (ϕ : μML At (suc n))
           → (expand Γ ϕ) [ μMLη op (expand Γ ϕ) ] ≡ expand Γ (ϕ [ μMLη op ϕ ])
sub-expand op [] ϕ =
  begin
    ((expand [] ϕ) [ μMLη op (expand [] ϕ) ])
  ≡⟨ cong (λ a → a [ μMLη op a ]) (sym $ expand-nil ϕ) ⟩
    (ϕ [ μMLη op ϕ ])
  ≡⟨ expand-nil (ϕ [ μMLη op ϕ ]) ⟩
    expand [] (ϕ [ μMLη op ϕ ])
  ∎ where open ≡-Reasoning
sub-expand op (ψ ,- Γ) ϕ =
  begin
    (expand (ψ ,- Γ) ϕ [ μMLη op (expand (ψ ,- Γ) ϕ) ])
  ≡⟨ cong (λ a → a [ μMLη op a ]) (expand-cons' Γ ψ ϕ)  ⟩
    (expand Γ (sub (sub-n' 1 ψ) ϕ) [ μMLη op (expand Γ (sub (sub-n' 1 ψ) ϕ)) ])
  ≡⟨ sub-expand op Γ (ϕ [ ψ ]') ⟩
    expand Γ ((ϕ [ ψ ]') [ μMLη op ϕ [ ψ ] ])
  ≡⟨ cong (expand Γ) (sym $ substitution-lemma ϕ (μMLη op ϕ) ψ) ⟩
    expand Γ ((ϕ [ μMLη op ϕ ]) [ ψ ])
  ≡⟨ expand-cons Γ ψ (ϕ [ μMLη op ϕ ]) ⟨
    expand (ψ ,- Γ) (ϕ [ μMLη op ϕ ])
  ∎ where open ≡-Reasoning

-- And in particular, the unfold of an expand is an expand.
unfold-expand : ∀ {At n} op (Γ : Scope At n) (ϕ : μML At (suc n))
              → unfold (μMLη op (expand Γ ϕ)) ≡ expand (μMLη op ϕ ,- Γ) ϕ
unfold-expand op Γ ϕ =
  begin
    unfold (μMLη op (expand Γ ϕ))
  ≡⟨ sub-expand op Γ ϕ ⟩
    expand Γ (ϕ [ μMLη op ϕ ])
  ≡⟨ expand-cons Γ (μMLη op ϕ) ϕ ⟨
    expand (μMLη op ϕ ,- Γ) ϕ
  ∎ where open ≡-Reasoning
