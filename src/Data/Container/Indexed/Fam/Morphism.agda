{-# OPTIONS --safe #-}
module Data.Container.Indexed.Fam.Morphism where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Maybe
open import Function
open import Relation.Binary.Isomorphism
open import Relation.Binary.PropositionalEquality hiding (J)

open import Data.Container.Indexed.Fam.Base as Cont
open import Data.Container.Indexed.Fam.Combinator.Base


open Container

private variable
  I J : Set
  C D : Container I J

record _⇒_ (C : Container I J) (D : Container I J) : Set where
  constructor _▷_
  field
    fw : ∀ {j} → Shape C j → Shape D j
    bw : ∀ {j} {s : Shape C j} → ∀ {i} → Position D (fw s) i → Position C s i

  -- Meaning of an indexed dependent lens. AKA functoriality of ⟦_⟧
  ⟪_⟫ : {P : I → Set}
      → ∀ {j} → ⟦ C ⟧ P j → ⟦ D ⟧ P j
  ⟪_⟫ (s , p) = fw s , p ∘ bw
open _⇒_ public
infixr 20 _⇒_

-- ⟦_⟧ is a functor from containers to endofunctors on sets.
-- This predicate expresses that a given set function is in
-- the image of that functor. This means that the
-- function is a natural transformation on set endofunctors.
IsNatural : (P : I → Set) (j : J)
          → (f : ⟦ C ⟧ P j → ⟦ D ⟧ P j)
          → Set
IsNatural {C = C} {D = D} P j f = Σ[ f' ∈ C ⇒ D ] (⟪ f' ⟫ {P} ≗ f) where open _⇒_


⟨⊥-elim⟩ : ⟨⊥⟩ ⇒ C
⟨⊥-elim⟩ = ⊥-elim ▷ λ { {s = ()} }

