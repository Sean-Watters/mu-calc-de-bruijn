
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Rational.Tree.Flattening
  {X : Set}
  (_≟_ : Decidable (_≡_ {A = X})) where

open import Data.FreshList.InductiveInductive
-- open import Data.FreshList.UniqueList.Base
open import Data.FreshList.UniqueList.Neq _≟_


-----------------------------------------------------
-- Flattening to Fresh List, and Deduplicated Size --
-----------------------------------------------------

-- flatten : ∀ {n} → Tree X n → SortedList
