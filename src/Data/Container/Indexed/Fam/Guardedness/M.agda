{-# OPTIONS --safe --guardedness #-}

-- From Indexed Containers, Altenkirch et al 2015
module Data.Container.Indexed.Fam.Guardedness.M where

open import Codata.Musical.Notation using (♭; ∞; ♯_)
open import Data.Container.Indexed.Fam.Base

data M {I : Set} (C : Container I I) : I → Set where
  inf : ∀ {i} → ⟦ C ⟧ (λ i → ∞ (M C i)) i → M C i
