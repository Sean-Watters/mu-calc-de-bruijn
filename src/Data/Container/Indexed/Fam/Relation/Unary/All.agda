{-# OPTIONS --safe #-}

module Data.Container.Indexed.Fam.Relation.Unary.All where

open import Data.Product

open import Data.Container.Indexed.Fam.Base

record □ {I J : Set} (C : Container I J) {P : I → Set}
         (Q : ∀ {i} → P i → Set) {j : J} (c : ⟦ C ⟧ P j) : Set where
    constructor all
    field proof : ∀ {i : I} {p : Position C {j} (proj₁ c) i} → Q (proj₂ c p)
