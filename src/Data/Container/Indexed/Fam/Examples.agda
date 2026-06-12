
module Data.Container.Indexed.Fam.Examples where

open import Data.Container.Indexed.Fam.Base

open import Axiom.Extensionality.Propositional
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Fin
open import Data.Product
open import Data.Sum
open import Function
open import Relation.Binary.Isomorphism
open import Relation.Binary.PropositionalEquality

-- Vectors are a particularly degenerate example of indexed container because the indexing set
-- is exactly the shapes.
module Vec (ext : ∀ {a b} → Extensionality a b) where
  open import Data.Vec
  open import Data.Vec.Properties

  ⟨Vec⟩ : Container ⊤ ℕ
  ⟨Vec⟩ .Shape n = ⊤
  ⟨Vec⟩ .Position {n} _ _ = Fin n
  
  vec-iso : ∀ {X : Set}
          → ∀ n → ⟦ ⟨Vec⟩ ⟧ (const X) n ≃ Vec X n
  vec-iso n .to (k , f) = tabulate f
  vec-iso n .from xs = _ , lookup xs
  vec-iso n .from-to (tt , f) = cong (tt ,_) (implicit-extensionality ext (ext (sym ∘ lookup∘tabulate f)))
  vec-iso n .to-from = sym ∘ tabulate∘lookup
  

module Lasso where
  
  data WeirdNat : Set where
    true : WeirdNat
    false : WeirdNat
    succ : WeirdNat → WeirdNat

  -- ignoring the indexing, this is `ℕ × (1 + Fin n)`
  data LassoShape (n : ℕ) : Set where
    zero : LassoShape n
    succ : LassoShape (suc n) → LassoShape n
    loop : Fin n → LassoShape n

  -- data Lasso (n : ℕ) (X : Set) : ℕ → Set where
  --   [] : Lasso n X 0
  --   _∷_ : ∀ {m} → X → Lasso (suc n) X m → Lasso n X (suc m)
  --   loop : Fin n → Lasso n X n
    
  data Lasso (n : ℕ) (X : Set) : Set where
    [] : Lasso n X
    _∷_ : X → Lasso (suc n) X → Lasso n X
    loop : Fin n → Lasso n X



  ⟨Lasso⟩ : Container {!!} ℕ
  ⟨Lasso⟩ .Shape = LassoShape
  ⟨Lasso⟩ .Position x x₁ = {!!}
