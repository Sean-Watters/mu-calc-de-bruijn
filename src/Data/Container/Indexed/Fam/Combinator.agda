{-# OPTIONS --safe #-}

module Data.Container.Indexed.Fam.Combinator where

open import Level using (Level) renaming (suc to lsuc)
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Function hiding (force)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Relation.Binary.Isomorphism

open import Data.Container.Indexed.Fam.Base
open Container

private
  variable
    I J : Set

-- The Identity Container.

⟨id⟩ : Container J J
⟨id⟩ = const ⊤ ▷ λ {i} _ j → i ≡ j

-- The Constant Container.

⟨const⟩ : (J → Set) → Container I J
⟨const⟩ P = P ▷ (const (const ⊥))

-- The Empty Container
⟨⊥⟩ : Container I J
⟨⊥⟩ = ⟨const⟩ (const ⊥)

-- The Unit Container
⟨⊤⟩ : Container I J
⟨⊤⟩ = ⟨const⟩ (const ⊤)

-- Binary Product.
-- Shapes are pairs of shapes from the left and right;
-- Positions are a *choice* of a left position or a right position.

_⟨×⟩_ : Container I J → Container I J → Container I J
(S ▷ P) ⟨×⟩ (T ▷ Q) = (λ j → S j × T j)
                    ▷ (λ x i → (P (proj₁ x) i) ⊎ (Q (proj₂ x) i))

-- Indexed Product.
-- Generalisation of binary product to indexing sets other than Bool.
-- And in fact, to indexing sets which are dependent on J.

⟨Π⟩ : {X : J → Set} → (∀ {j} → X j → Container I J) → Container I J
⟨Π⟩ {X = X} P = (λ j → (x : X j) → Shape (P x) j)
              ▷ (λ {j} Q i → Σ[ x ∈ X j ] Position (P x) (Q x) i )

-- The version where the product is indexed by a simple type X
-- ⟨Π⟩ : {X : Set} → (X → Container I J) → Container I J
-- ⟨Π⟩ {X = X} P = (λ j → (x : X) → Shape (P x) j)
--               ▷ (λ Q i → Σ[ x ∈ X ] Position (P x) (Q x) i )

-- Binary Sum.
-- Shapes are either a shape from the left or right.
-- The choice of shape *determines* where you must take a position from.

_⟨+⟩_ : Container I J → Container I J → Container I J
(S ▷ P) ⟨+⟩ (T ▷ Q) = (λ j → S j ⊎ T j)
                    ▷ [ P , Q ]

-- Indexed Sum.
-- Generalisation of binary sum to arbirary indexing sets (possibly
-- dependent on J)


⟨Σ⟩ : (X : J → Set) → (∀ {j} → X j → Container I J) → Container I J
⟨Σ⟩ X P = (λ j → Σ[ x ∈ X j ] Shape (P x) j)
              ▷ (λ { (x , s) i → Position (P x) s i })

-- The version where X is a simple type
-- ⟨Σ⟩ : {X : Set} → (X → Container I J) → Container I J
-- ⟨Σ⟩ {X = X} P = (λ j → Σ[ x ∈ X ] Shape (P x) j)
--               ▷ (λ { (x , s) i → Position (P x) s i })

