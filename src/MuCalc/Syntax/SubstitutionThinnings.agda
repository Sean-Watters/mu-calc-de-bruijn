{-# OPTIONS --safe #-}
module MuCalc.Syntax.SubstitutionThinnings where

open import Data.Nat
open import Data.Product
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

open import Function using (_∘_)

open import MuCalc.Base



---------------
-- Thinnings --
---------------

-- A `Thin i j` is a bit vector of length `j`, with `i` many 1's.
-- It represents an order-preserving injection `Fin i -> Fin j`.
data Thin : ℕ → ℕ → Set where
  keep : ∀ {i j} → Thin i j → Thin (suc i) (suc j) -- 1 ∷_
  drop : ∀ {i j} → Thin i j → Thin i (suc j)       -- 0 ∷_
  end : Thin 0 0                                   -- ε

-- We define Fin in terms of thinnings. A `Fin n` is a way of choosing
-- 1 point from n points.
Fin : ℕ → Set
Fin = Thin 1

-- The identity thinning; all 1's.
full : ∀ {i} → Thin i i
full {zero} = end
full {suc i} = keep full

---------------------------
-- Parallel Substitution --
---------------------------

Subst : Set → ℕ → ℕ → Set
Subst At i j = Fin i → μML At j
