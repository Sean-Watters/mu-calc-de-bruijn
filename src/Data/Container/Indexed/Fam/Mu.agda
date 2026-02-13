{-# OPTIONS --safe #-}
module Data.Container.Indexed.Fam.Mu where

open import Data.Sum
open import Data.Product

open import Data.Container.Indexed.Fam.Base
open import Data.Container.Indexed.Fam.W
open Container

data Path {I J : Set}
          (S : J → Set)
          (PI : {j : J} → S j → I → Set)
          (PJ : {j : J} → S j → J → Set)
          : {j : J} → W (S ▷ PJ) j → I → Set where
  path : {j : J} {s : S j} {f : {j : J} → PJ s j → W (S ▷ PJ) j} {i : I}
       → PI s i
       ⊎ (Σ[ j' ∈ J ] Σ[ p ∈ PJ s j' ] Path S PI PJ (f p) i)
       → Path S PI PJ (sup (s , f)) i

⟨μ⟩ : {I J : Set} →  Container (I ⊎ J) J → Container I J
⟨μ⟩ {I} {J} (S ▷ P) =
  let PI : {j : J} → S j → I → Set
      PI s i = P s (inj₁ i)

      PJ : {j : J} → S j → J → Set
      PJ s j = P s (inj₂ j)

  in (W (S ▷ PJ)) ▷ Path S PI PJ
