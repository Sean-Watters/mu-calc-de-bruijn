
module Data.Sum.MoreProps where

open import Level
open import Data.Maybe
open import Data.Sum
open import Relation.Binary.PropositionalEquality

private variable
  ℓ : Level

isInj₂-lemma : ∀ {X Y : Set ℓ} (p : X ⊎ Y)
             → isInj₂ p ≡ nothing
             → X
isInj₂-lemma (inj₁ x) refl = x
