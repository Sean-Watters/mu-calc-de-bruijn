
open import Relation.Binary.PropositionalEquality
open import Relation.Binary

module Data.FreshList.UniqueList.Neq {X : Set} (_≟_ : Decidable (_≡_ {A = X})) where

open import Relation.Nullary
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Algebra.Structures.OICM

import Data.FreshList.UniqueList.Base as UniqueList


≢-apartness : IsApartnessRelation {A = X} _≡_ _≢_
≢-apartness .IsApartnessRelation.irrefl p ¬p = ¬p p
≢-apartness .IsApartnessRelation.sym ¬p p = ¬p (sym p)
≢-apartness .IsApartnessRelation.cotrans {x = x} {y} x≢y z with x ≟ z
... | no ¬p = inj₁ ¬p
... | yes refl = inj₂ x≢y

≢-dne : ∀ {x y : X} → ¬ (x ≢ y) → x ≡ y
≢-dne {x} {y} ¬¬p with x ≟ y
... | yes p = p
... | no ¬p = ⊥-elim (¬¬p ¬p)

≢-dec : Decidable (_≢_ {A = X})
≢-dec x y with x ≟ y
... | yes p = no λ ¬p → ¬p p
... | no ¬p = yes ¬p

≢-pda : IsPropDecTightApartnessRelation {X} _≡_ _≢_
≢-pda .IsPropDecTightApartnessRelation.isEquivalence = isEquivalence
≢-pda .IsPropDecTightApartnessRelation.isAR = ≢-apartness
≢-pda .IsPropDecTightApartnessRelation.prop _ _ = refl
≢-pda .IsPropDecTightApartnessRelation.tight x y = ≢-dne , (λ p ¬p → ¬p p)
≢-pda .IsPropDecTightApartnessRelation.dec = ≢-dec

open UniqueList {X} {_≡_} {_≢_} ≢-pda
