{-# OPTIONS --guardedness #-}

module Data.Container.Combinator.Nu where

open import Level
open import Codata.Guarded.M
open import Data.Sum
open import Data.Product
open import Data.Container

private variable
  ℓs ℓp : Level

-- M-types are possibly infinite trees, so paths through them are co-lists
-- whiiiiich means this is probably incorrect? This looks like it should only give the finite paths
data CoPath (S : Set ℓs)
            (P : S → Set ℓp)
            : M (S ▷ P) → Set (ℓs ⊔ ℓp) where
  copath : {s : S} {f :  P s → M (S ▷ P)}
         → P s ⊎ (Σ[ p ∈ P s ] CoPath S P (f p))
         → CoPath S P (inf s f)

-- ⟨ν⟩ : {I J : Set} → Container (I ⊎ J) J → Container I J
-- ⟨ν⟩ {I} {J} (S ◃ P) =
--   let PI : {j : J} → S j → I → Set
--       PI s i = P s (inj₁ i)

--       PJ : {j : J} → S j → J → Set
--       PJ s j = P s (inj₂ j)

--   in M (S ◃ PJ) ∞ ◃ CoPath S PI PJ ∞
