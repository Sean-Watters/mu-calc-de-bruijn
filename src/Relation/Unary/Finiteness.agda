open import Relation.Binary

module Relation.Unary.Finiteness {a b} (X : Setoid a b) where

open import Level
open import Data.List
open import Data.Product
open import Data.List.Membership.Setoid X
open import Algebra.Structures.Propositional

open Setoid

is-enumeration : (L : List (Carrier X)) → Set (a ⊔ b)
is-enumeration L = (x : Carrier X) → x ∈ L

-- An enumerated type is one where there exists some list
-- L which contains all of the elements of the type.
Enumerated : Set (a ⊔ b)
Enumerated = ∃[ L ] (is-enumeration L)


{-
-- Another way to formalise enumeration is to say X is isomorphic to some finite prefix of ℕ.
-- The two variants can be shown to be isomorphic.
Enumerated' : Set (a ⊔ b)
Enumerated' = ∃[ n ] (Carrier X ≃ Fin n)

-- A bounded type is one for which all lists larger than some n : ℕ must contain duplicates.
-- This is weaker a notion than enumeration, as it doesn't give us a way to choose any elements of X.
Bounded : Set (a ⊔ b)
Bounded = ∃[ n ] ((xs : Vec≤ X n) → ¬ Unique (vec xs)) where open Vec≤
-- todo: would it be better to phrase "contains duplicates" in a positive way?
-}
