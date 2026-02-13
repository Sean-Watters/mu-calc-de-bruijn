{-# OPTIONS --sized-types #-}
module Data.Container.Indexed.Fam.SizedTypes.M where

open import Size
open import Codata.Sized.Thunk using (Thunk; force)

open import Data.Container.Indexed.Fam.Base

-- Indexed M-types.
-- Dual to W-types; so this is the way to generate families of
-- coinductive codata types from indexed containers.
-- In general we get possibly-infinite trees.
data M {J : Set} (C : Container J J) (κ : Size) : J → Set where
  inf :  ∀ {j} → ⟦ C ⟧ (λ j' → Thunk (λ α → M C α j) κ) j → M C κ j
