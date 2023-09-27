module Relation.Unary.Countable where

open import Relation.Binary.Isomorphism
open import Data.Nat

IsCountable : Set → Set
IsCountable X = X ≃ ℕ
