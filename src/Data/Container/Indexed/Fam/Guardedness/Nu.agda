{-# OPTIONS --guardedness #-}

module Data.Container.Indexed.Fam.Guardedness.Nu where

open import Data.Container.Indexed.Fam.Guardedness.M

open import Axiom.Extensionality.Propositional using (Extensionality) renaming (implicit-extensionality to exti)
open import Level
open import Codata.Musical.Notation
open import Data.Sum
open import Data.Product

open import Data.Container.Indexed.Fam.Base
open import Data.Container.Indexed.Fam.Guardedness.M


-- M-types are possibly infinite trees, so paths through them are co-lists
data CoPath {I J : Set}
            (S : J → Set)
            (PI : {j : J} → S j → I → Set)
            (PJ : {j : J} → S j → J → Set)
            : {j : J} → M (S ◁ PJ) j → I → Set where
  copath : {j : J} {s : S j} {f : {j' : J} → PJ s j' → ∞ (M (S ◁ PJ) j')} {i : I}
         → PI s i
         ⊎ (Σ[ j' ∈ J ] Σ[ p ∈ PJ s j' ] CoPath S PI PJ (♭ (f p)) i)
         → CoPath S PI PJ (inf (s , f)) i

⟨ν⟩ : {I J : Set} → Container (I ⊎ J) J → Container I J
⟨ν⟩ {I} {J} (S ◁ P) =
  let PI : {j : J} → S j → I → Set
      PI s i = P s (inj₁ i)

      PJ : {j : J} → S j → J → Set
      PJ s j = P s (inj₂ j)

  in M (S ◁ PJ) ◁ CoPath S PI PJ
