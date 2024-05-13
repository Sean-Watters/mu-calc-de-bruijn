open import Algebra.Structure.OICM

module Free.IdempotentCommutativeMonoid.Fixpoints
  {X : Set} {_≈_ : X -> X -> Set} {_<_ : X -> X -> Set}
  (<-STO : IsPropStrictTotalOrder _≈_ _<_)
  where

open import Level
open import Data.List as L using (List; []; _∷_) renaming (_++_ to _++L_)
open import Data.List.Relation.Unary.Any
open import Data.Product
open import Relation.Unary.Finiteness
open import Relation.Binary

open import Data.FreshList.InductiveInductive
open import Free.IdempotentCommutativeMonoid.Base <-STO
open import Free.IdempotentCommutativeMonoid.Properties <-STO

X-setoid : Setoid 0ℓ 0ℓ
Setoid.Carrier X-setoid = X
Setoid._≈_ X-setoid = _≈_
Setoid.isEquivalence X-setoid = IsPropStrictTotalOrder.isEquivalence <-STO

SortedList-setoid : Setoid 0ℓ 0ℓ
Setoid.Carrier SortedList-setoid = SortedList
Setoid._≈_ SortedList-setoid = _≈L_
Setoid.isEquivalence SortedList-setoid = isEquivalence

open import Data.List.Membership.Setoid SortedList-setoid renaming (_∈_ to _∈L_)

-- We assume a finite carrier set
module _ (X-fin : Enumerated X-setoid) where

    private
      X-enum = proj₁ X-fin

    powerset : List SortedList
    powerset = go X-enum
      module Pow where
      go : List X → List SortedList
      go [] = [] ∷ []
      go (x ∷ xs) = let Pxs = go xs
                    in Pxs ++L L.map (insert x) Pxs

    powerset-isEnum : is-enumeration SortedList-setoid powerset
    powerset-isEnum [] = lem X-enum where
      lem : ∀ x → [] ∈L Pow.go x
      lem [] = here []
      lem (x ∷ xs) = {!lem xs!} -- "inl" of that
    powerset-isEnum (cons x xs x#xs) = {!proj₂ X-fin x!}

    prefixedpoints : (SortedList → SortedList) → List SortedList
    prefixedpoints f = {!!} where
