{-# OPTIONS --safe #-}
module MuCalc.Thinning.Base where

open import Data.Nat hiding (_≟_)
open import Data.Thinning as Th
open import Data.Empty renaming (⊥ to Zero)
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Decidable

--------------------------------------------------------------

data Opη : Set where
  mu : Opη
  nu : Opη

data Op₀ (At : Set) : Set where
  tt : Op₀ At
  ff : Op₀ At
  at  : At → Op₀ At
  ¬at : At → Op₀ At

data Op₁ : Set where
  box : Op₁
  dia : Op₁

data Op₂ : Set where
  and : Op₂
  or : Op₂

-- Formulas are parameterised by the list of names in scope.
data μML (At : Set) (n : ℕ) : Set where
  var : Fin n → μML At n
  μML₀ : (op : Op₀ At) → μML At n
  μML₁ : (op : Op₁) → (ϕ : μML At n) → μML At n
  μML₂ : (op : Op₂) → (ϕ : μML At n) → (ψ : μML At n) → μML At n
  μMLη : (op : Opη) → (ϕ : μML At (suc n)) → μML At n

data IsFP {At : Set} : {n : ℕ} (ϕ : μML At n) → Set where
  instance fp : {n : ℕ} {op : Opη} {ψ : μML At (suc n)} → IsFP (μMLη op ψ)

-- Some prettier pattern synonyms
pattern ⊤ = μML₀ tt
pattern ⊥ = μML₀ ff
pattern lit x = μML₀ (at x)
pattern ¬lit x = μML₀ (¬at x)
pattern ■ ϕ = μML₁ box ϕ
pattern ◆ ϕ = μML₁ dia ϕ
pattern _∧_ ϕ ψ = μML₂ and ϕ ψ
pattern _∨_ ϕ ψ = μML₂ or ϕ ψ
pattern μ ϕ = μMLη mu ϕ
pattern ν ϕ = μMLη nu ϕ


--------------------------------------------------------------

-- -- Negation is derived by de Morgan substitutions.
-- ¬ : ∀ {At n} → μML At n → μML At n
-- ¬ (var x)        = var x -- is this right?
-- ¬ ⊤ = ⊥
-- ¬ ⊥ = ⊤
-- ¬ (μML₀ (at x)) = μML₀ (¬at x)
-- ¬ (μML₀ (¬at x)) = μML₀ (at x)
-- ¬ (■ ϕ) = ◆ (¬ ϕ)
-- ¬ (◆ ϕ) = ■ (¬ ϕ)
-- ¬ (ϕ ∧ ψ) = (¬ ϕ) ∨ (¬ ψ)
-- ¬ (ϕ ∨ ψ) = (¬ ϕ) ∧ (¬ ψ)
-- ¬ (μ ϕ) = ν (¬ ϕ)
-- ¬ (ν ϕ) = μ (¬ ϕ)

-- -- Material implication
-- _⇒_ : ∀ {At n} → μML At n → μML At n → μML At n
-- ϕ ⇒ ψ = μML₂ or (¬ ϕ) ψ


-------------
--  Scopes --
-------------

-- Vectors of formulas, where the index of the formula depends on its position in the vector.
data Scope (At : Set) : ℕ → Set where
  [] : Scope At zero
  _,-_ : ∀ {n} → (ϕ : μML At n) (Γ : Scope At n) → Scope At (suc n)

infixr 10 _,-_
