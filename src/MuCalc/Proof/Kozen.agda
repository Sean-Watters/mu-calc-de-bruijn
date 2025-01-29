open import Algebra.Structures.Propositional
open import Relation.Binary.PropositionalEquality

module MuCalc.Proof.Kozen
  {At : Set}
  {_<A_ : At → At → Set}
  (<A-STO : IsPropStrictTotalOrder _≡_ _<A_)
  where

open import Data.Empty using (⊥)
open import Data.Nat
open import Data.Product
open import MuCalc.Base renaming (⊤ to ⊤'; ⊥ to ⊥')


{-
-- Hilbert-style axiomatisation of the mu-calculus from Yde's paper.
-- The use of ⇒ and ¬ is a bad smell though, since neither are primitive for us.
data ⊢_ : ∀ {i} → μML At i → Set where
  -- Rules
  -- MP : ∀ {i} {ϕ ψ : μML At i} → ⊢ ϕ → ⊢  (ϕ ⇒ ψ) → ⊢ ψ
  N  : ∀ {i} {ϕ   : μML At i} → ⊢  ϕ → ⊢ (■ ϕ)

  -- -- Axioms
  -- P1 : ∀ {i} {ϕ ψ   : μML At i} → ⊢ (ϕ ⇒ (ψ ⇒ ϕ))
  -- P2 : ∀ {i} {ϕ ψ χ : μML At i} → ⊢ ((ϕ ⇒ (ψ ⇒ χ)) ⇒ ((ϕ ⇒ ψ) ⇒ (ϕ ⇒ χ)))
  -- P3 : ∀ {i} {ϕ ψ   : μML At i} → ⊢ ((¬ ϕ ⇒ ¬ ψ) ⇒ (ψ ⇒ ϕ))
  -- K  : ∀ {i} {ϕ ψ   : μML At i} → ⊢ (■ (ϕ ⇒ ψ) ⇒ (■ ϕ ⇒ ■ ψ))

  -- The mu extension
  Aμ : ∀ {i} n {ϕ   : μML At i} → ⊢ (sub ϕ n ϕ ⇒ μ (inject₁ ϕ))  -- the prefixpoint axoim schema
  Rμ : ∀ {i} n {ϕ ψ : μML At i} → ⊢ (sub ϕ n ψ ⇒ ψ) → ⊢ (μ (inject₁ ϕ) ⇒ ψ) -- the prefixpoint rule

-}
