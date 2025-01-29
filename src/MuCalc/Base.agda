{-# OPTIONS --safe #-}
module MuCalc.Base where

open import Data.Nat hiding (_≟_)
open import Data.Fin as F using (Fin; _≟_) renaming (_ℕ-ℕ_ to _-_)
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

-- Vectors of formulas, with two added tricks:
-- * The index of the formula depends on its position in the vector
-- * We allow the front of the scope to potentially coontain dummies. This is to faciliatate the definition of the expansion map,
--   where we want to instantiate variables that were already free but leave previously bound variables alone.
data Scope (At : Set) : ℕ → Set where
  [] : Scope At zero
  _,-_ : ∀ {n} → (ϕ : μML At n) (Γ : Scope At n) → Scope At (suc n)

lookup : ∀ {At n} → (Γ : Scope At n) → (x : Fin n) → μML At (n - (F.suc x))
lookup (ϕ ,- Γ) F.zero = ϕ
lookup (ϕ ,- Γ) (F.suc x) = lookup Γ x

unwind : ∀ {At n} → (Γ : Scope At n) → (x : Fin n) → Scope At (n - (F.suc x))
unwind (ϕ ,- Γ) F.zero = Γ
unwind (ϕ ,- Γ) (F.suc x) = unwind Γ x
