{-# OPTIONS --sized-types #-}
module Data.Container.Indexed.Fam.SizedTypes where

open import Axiom.Extensionality.Propositional using (Extensionality) renaming (implicit-extensionality to exti)
open import Level
open import Size
open import Codata.Sized.Thunk using (Thunk; force)
open import Data.Sum
open import Data.Product
open import Data.Container.Indexed.Fam

-- Indexed M-types.
-- Dual to W-types; so this is the way to generate families of
-- coinductive codata types from indexed containers.
-- In general we get possibly-infinite trees.
data M {J : Set} (C : Container J J) (κ : Size) : J → Set where
  inf :  ∀ {j} → ⟦ C ⟧ (λ j' → Thunk (λ α → M C α j) κ) j → M C κ j



-- M-types are possibly infinite trees, so paths through them are co-lists
data CoPath {I J : Set}
            (S : J → Set)
            (PI : {j : J} → S j → I → Set)
            (PJ : {j : J} → S j → J → Set)
            (κ : Size)
            : {j : J} → M (S ◃ PJ) κ j → I → Set where
  copath : {j : J} {s : S j} {f : {j' : J} → PJ s j' → Thunk (λ α → M (S ◃ PJ) α j) ∞} {i : I}
         → PI s i
         ⊎ (Σ[ j' ∈ J ] Σ[ p ∈ PJ s j' ] CoPath S PI PJ κ (force (f p)) i)
         → CoPath S PI PJ κ (inf (s , f)) i

⟨ν⟩ : {I J : Set} → Container (I ⊎ J) J → Container I J
⟨ν⟩ {I} {J} (S ◃ P) =
  let PI : {j : J} → S j → I → Set
      PI s i = P s (inj₁ i)

      PJ : {j : J} → S j → J → Set
      PJ s j = P s (inj₂ j)

  in M (S ◃ PJ) ∞ ◃ CoPath S PI PJ ∞


-- module Correctness (ext : Extensionality 0ℓ 0ℓ) where
--   correct : {I : Set}(X : I → Set) → {!!}
--   correct = {!!}
