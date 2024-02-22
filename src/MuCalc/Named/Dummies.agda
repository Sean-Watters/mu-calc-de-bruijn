open import Algebra.Structures.Propositional
open import Relation.Unary.Countable
open import Relation.Binary.PropositionalEquality

module MuCalc.Named.Dummies
  {At Var : Set}
  {_<A_ : At → At → Set}
  {_<V_ : Var → Var → Set}
  (<A-STO : IsPropStrictTotalOrder _≡_ _<A_)
  (<V-STO : IsPropStrictTotalOrder _≡_ _<V_)
  (At-countable : IsCountable At)
  (Var-countable : IsCountable Var)
  where

open import Data.Nat
open import Data.FreshList.InductiveInductive
open import Free.IdempotentCommutativeMonoid.Base <V-STO
open import Free.IdempotentCommutativeMonoid.Properties <V-STO

open import MuCalc.Named.Base <A-STO <V-STO At-countable Var-countable
open import MuCalc.Named.Contexts <A-STO <V-STO At-countable Var-countable

---------------------------
-- Formulas with Dummies --
---------------------------

-- This mirrors the core type of mu calculus formulas, with the addition
-- of "dummy" subformulas, labelled by the formula they represent.
-- Defined mutually with the view on fixpoint formulas with dummies.
mutual
  data μMLε (Γ : SortedList) : Set where
    var : (x : Var) → x ∈ Γ → μMLε Γ
    μML₀ : Op₀ → μMLε Γ
    μML₁ : Op₁ → μMLε Γ → μMLε Γ
    μML₂ : Op₂ → μMLε Γ → μMLε Γ → μMLε Γ
    μMLη : Opη → (x : Var) → μMLε (insert x Γ) → μMLε Γ
    ε : {ψ : μMLε []} → μFPε ψ → μMLε Γ

  data μFPε {Γ : SortedList} : μMLε Γ → Set where
    fp : (op : Opη) → (x : Var) → (ϕ : μMLε (insert x Γ)) → μFPε (μMLη op x ϕ)


binderOfε : ∀ {Γ} {ϕ : μMLε Γ} → μFPε ϕ → Var
binderOfε (fp op x ϕ) = x

-- The length of a formula, not counting dummies
lenε : ∀ {Γ} -> μMLε Γ -> ℕ
lenε (var x x∈Γ) = 1
lenε (μML₀ op) = 1
lenε (μML₁ op ψ) = suc (lenε ψ)
lenε (μML₂ op ψ ϕ) = suc (lenε ψ + lenε ϕ)
lenε (μMLη op x ψ) = suc (lenε ψ)
lenε (ε ϕ) = 0 -- we don't need to look inside dummies because they always are already in the closure, and therefore they don't need fuel allocated

-------------------------------------------
-- Embedding and Erasure (Instantiation) --
-------------------------------------------

embed : ∀ {Γ} → μML Γ → μMLε Γ
embed (var x p) = var x p
embed (μML₀ op) = μML₀ op
embed (μML₁ op ψ) = μML₁ op (embed ψ)
embed (μML₂ op ψ ϕ) = μML₂ op (embed ψ) (embed ϕ)
embed (μMLη op x ψ) = μMLη op x (embed ψ)

-- "Erasing" the dummies. A better name would be "instantiation",
-- because we replace the dummy by the formula that labelled it.
erase : ∀ {Γ} → μMLε Γ → μML Γ
erase (var x p) = var x p
erase (μML₀ op) = μML₀ op
erase (μML₁ op ϕ) = μML₁ op (erase ϕ)
erase (μML₂ op ϕ ψ) = μML₂ op (erase ϕ) (erase ψ)
erase (μMLη op x ϕ) = μMLη op x (erase ϕ)
erase {Γ} (ε {ϕ} _) = weaken (erase ϕ) ⊆-[]-initial

-- erase is a one-sided inverse to embed.
erase-embed : ∀ {Γ} → (ϕ : μML Γ) → erase (embed ϕ) ≡ ϕ
erase-embed (var x x∈Γ) = refl
erase-embed (μML₀ op) = refl
erase-embed (μML₁ op ϕ) = cong (μML₁ op) (erase-embed ϕ)
erase-embed (μML₂ op ϕ ψ) = cong₂ (μML₂ op) (erase-embed ϕ) (erase-embed ψ)
erase-embed (μMLη op x ϕ) = cong (μMLη op x) (erase-embed ϕ)
-- This doesn't work the other way around; after you erase, you don't know whether
-- to send a fixpoint back to a fixpoint or a dummy.
