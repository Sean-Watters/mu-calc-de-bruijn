{-# OPTIONS --safe #-}
module MuCalc.DeBruijn.Syntax.Subformula where

open import Data.Nat
open import Data.Nat.Properties using (m≤n⇒m≤1+n; ≤-refl; ≤-trans)

open import MuCalc.DeBruijn.Base


-- The direct subformula relation
data SforD {At : Set} : {i j : ℕ} → i ≥ j → (ψ : μML At i) (ϕ : μML At j) → Set where
  down  : ∀ op {i} {p : i ≤ i} {ϕ : μML At i} → SforD p ϕ (μML₁ op ϕ)
  left  : ∀ op {i} {p : i ≤ i} {ϕl ϕr : μML At i} → SforD p ϕl (μML₂ op ϕl ϕr)
  right : ∀ op {i} {p : i ≤ i} {ϕl ϕr : μML At i} → SforD p ϕr (μML₂ op ϕl ϕr)
  under : ∀ op {i} {p : i ≤ suc i} {ϕ : μML At (suc i)} → SforD p ϕ (μMLη op ϕ)

-- The proper (ie, irreflexive) subformula relation
-- Can't use `Relation.Binary.Construct.Closure.Transitive` because of the indices
data SforNE {At : Set} : {i j : ℕ} → i ≥ j → μML At i → μML At j → Set where
  dsf  : ∀ {i j} (p : i ≥ j) {ϕ : μML At i} {ψ : μML At j}
       → SforD p ϕ ψ → SforNE p ϕ ψ
  cons : ∀ {i a j } (p : i ≥ a) (q : a ≥ j) (r : i ≥ j) {ϕ : μML At i} {α : μML At a} {ψ : μML At j}
       → SforD p ϕ α → SforNE q α ψ → SforNE r ϕ ψ
