{-# OPTIONS --safe #-}
module Data.Container.Indexed.Fam.Base where

-- The standard library uses so-called "pow-style" indexed
-- containers, where all the positions ("responses") live 
-- in one set, and you get a "next" function for picking out
-- their indices. This makes taking fixed points much harder, so
-- we instead use the "fam-style" presentation of Altenkirch et al,
-- with an indexed familty of positions.

open import Level using (Level) renaming (suc to lsuc)
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Function hiding (force)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Relation.Binary.Isomorphism

open import Data.Container.Indexed.Functors

----------
-- Base --
----------

-- Indexed containers, fam style
record Container (I J : Set) : Set₁ where
  constructor _◁_
  field
    Shape : Fam J
    Position : {j : J} → Shape j → Fam I
open Container public


-- The meaning/extension of a container is the indexed functor that it represents.
⟦_⟧ : {I J : Set} → Container I J → IFunc* I J
⟦ S ◁ P ⟧ F j = Σ[ s ∈ S j ] (∀ {i} → P s i → F i)

-- And it actually is a functor
⟦_⟧-map : {I J : Set}
        → (C : Container I J)
        → IFunc*-map (⟦ C ⟧)
        -- → {X Y : I → Set}
        -- → (∀ {i : I} → X i → Y i)
        -- → (∀ {j : J} → ⟦ C ⟧ X j  → ⟦ C ⟧ Y j)
⟦ C ⟧-map f i (s , g) = s , λ z → f _ (g z)


----------------
-- Reindexing --
----------------

-- (In the sense of reindexing)

-- In both indices
⟨bimap⟩ : {I I' J J' : Set} → (I' → I) → (J' → J) → Container I J → Container I' J'
⟨bimap⟩ f g (S ◁ P) = (S ∘ g) ◁ (λ s → P s ∘ f)


-- In I
⟨mapI⟩ : {I I' J : Set} → (I' → I) → Container I J → Container I' J
⟨mapI⟩ f = ⟨bimap⟩ f id

-- In J
⟨mapJ⟩ : {I J J' : Set} → (J' → J) → Container I J → Container I J'
⟨mapJ⟩ f = ⟨bimap⟩ id f

