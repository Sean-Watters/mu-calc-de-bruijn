module Data.Container.Combinator.Mu where

open import Level
open import Data.Sum
open import Data.Product
open import Data.Container
open import Data.W

private variable
  s p : Level

data Path {s p : Level} (S : Set s)
          (P : S → Set p)
          : W (S ▷ P) → Set (s ⊔ p) where
  path : {s : S} {f : P s → W (S ▷ P)}
       → P s ⊎ (Σ[ p ∈ P s ] Path S P (f p))
       → Path S P (sup (s , f))

⟨μ⟩ : Container s p → Container (s ⊔ p) (s ⊔ p)
⟨μ⟩ (S ▷ P) = (W (S ▷ P)) ▷ Path S P
