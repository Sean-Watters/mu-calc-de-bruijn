open import Algebra.Structures.Propositional
open import Relation.Unary.Countable
open import Relation.Binary.PropositionalEquality

module MuCalc.DeBruijn.Base
  {At : Set}
  {_<A_ : At → At → Set}
  (<A-STO : IsPropStrictTotalOrder _≡_ _<A_)
  (At-countable : IsCountable At)
  where

open import Data.Nat
open import Data.Fin

data Opη : Set where
  μ : Opη
  ν : Opη

data Op₀ : Set where
  ⊤ : Op₀
  ⊥ : Op₀
  at  : At → Op₀
  ¬at : At → Op₀

data Op₁ : Set where
  □ : Op₁
  ◆ : Op₁

data Op₂ : Set where
  ∧ : Op₂
  ∨ : Op₂

-- Formulas are parameterised by the list of names in scope.
data μML (n : ℕ) : Set where
  var : Fin n → μML n
  μML₀ : (op : Op₀) → μML n
  μML₁ : (op : Op₁) → (ϕ : μML n) → μML n
  μML₂ : (op : Op₂) → (ϕ : μML n) → (ψ : μML n) → μML n
  μMLη : (op : Opη) → (ϕ : μML (suc n)) → μML n
