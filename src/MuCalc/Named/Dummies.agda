open import Algebra.Structure.OICM
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

open import Data.FreshList.InductiveInductive
open import Free.IdempotentCommutativeMonoid.Base <V-STO
open import Free.IdempotentCommutativeMonoid.Properties <V-STO

open import MuCalc.Named.Base <A-STO <V-STO At-countable Var-countable

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

-------------------------------------------
-- Embedding and Erasure (Instantiation) --
-------------------------------------------

embed : ∀ {Γ} → μML Γ → μMLε Γ
embed (var x p) = var x p
embed (μML₀ op) = μML₀ op
embed (μML₁ op ψ) = μML₁ op (embed ψ)
embed (μML₂ op ψ ϕ) = μML₂ op (embed ψ) (embed ϕ)
embed (μMLη op x ψ) = μMLη op x (embed ψ)

-- -- "Erasing" the dummies. A better name would be "instantiation",
-- -- because we replace the dummy by the formula that labelled it.
-- erase : ∀ {Γ} → μMLε Γ → μML Γ
-- erase (var x p) = var x p
-- erase (μML₀ op) = μML₀ op
-- erase (μML₁ op ψ) = μML₁ op (erase ψ)
-- erase (μML₂ op ψ ϕ) = μML₂ op (erase ψ) (erase ϕ)
-- erase (μMLη op x ψ) = μMLη op x (erase ψ)
-- erase {Γ} (ε {ψ} _) = weaken-many ψ Γ
