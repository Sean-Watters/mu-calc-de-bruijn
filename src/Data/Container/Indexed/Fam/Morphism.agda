{-# OPTIONS --safe #-}
module Data.Container.Indexed.Fam.Morphism where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

open import Function

open import Data.Container.Indexed.Fam.Base as Cont
open import Data.Container.Indexed.Fam.Combinator


open Container

record _⇒_ {I J : Set} (C : Container I J) (D : Container I J) : Set where
  constructor _▷_
  field
    fw : ∀ {j} → Shape C j → Shape D j
    bw : ∀ {j} {s : Shape C j} → ∀ {i} → Position D (fw s) i → Position C s i

  -- Meaning of an indexed dependent lens. Look at the indexed containers paper, and the CT
  ⟪_⟫ : {P : I → Set}
      → ∀ {j} → ⟦ C ⟧ P j → ⟦ D ⟧ P j
  ⟪_⟫ (s , p) = fw s , p ∘ bw
open _⇒_ public

⟨⊥-elim⟩ : ∀ {I J} {C : Container I J} → ⟨⊥⟩ ⇒ C
⟨⊥-elim⟩ = ⊥-elim ▷ λ { {s = ()} }

