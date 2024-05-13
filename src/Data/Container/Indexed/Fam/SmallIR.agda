{-# OPTIONS --safe #-}

module Data.Container.Indexed.Fam.SmallIR where

open import Data.Container.Indexed.Fam

open import Data.Unit
open import Data.Empty

-- Dybjer-Setzer IR codes. *Small* IR because I and O are sets, not larger.
data IR (I O : Set) : Set₁ where
  ι : (o : O) → IR I O
  σ : (S : Set) → (K : S → IR I O) → IR I O
  δ : (P : Set) → (K : (P → I) → IR I O) → IR I O

toCont : ∀ {I O} → IR I O → Container I O
toCont (ι o) = (λ _ → ⊤) ◃ λ _ _ → ⊥
toCont (σ S K) = {!!}
toCont (δ P KJ) = {!!}
