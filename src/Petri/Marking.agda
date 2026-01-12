
open import Data.Nat as ℕ using (ℕ)

module Petri.Marking (Place : ℕ) where

open import Data.Nat.Properties as ℕ using ()
open import Data.Nat.Minus as ℕ using ()
open import Data.Vec as Vec
open import Data.Vec.Relation.Binary.Pointwise.Inductive as VecPw using (Pointwise)
open import Data.Vec.Extras as Vec
open import Relation.Nullary


Marking = Vec ℕ Place

_≤_ : Marking → Marking → Set
_≤_ = VecPw.Pointwise ℕ._≤_
--∀ p → m p ℕ.≤ m' p

_≤?_ : ∀ m n → Dec (m ≤ n)
_≤?_ = VecPw.decidable ℕ._≤?_

subtract-markings : {n m : Marking} → n ≤ m → Marking
subtract-markings {n} {m} p = Vec.pointwise-minus n m p

add-markings : Marking → Marking → Marking
add-markings = Vec.zipWith ℕ._+_
