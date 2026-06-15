{-# OPTIONS --safe #-}
-- Labelled transition systems
module Data.LTS.Core where

open import Level
open import Data.Product
open import Function

private variable
  ℓs ℓl ℓt : Level

record LTS (ℓs ℓl ℓt : Level) : Set (suc (ℓs ⊔ ℓl ⊔ ℓt)) where
  field
    State : Set ℓs
    Label : Set ℓl
    _-[_]->_ : State -> Label -> State -> Set ℓt

IsSim : (lts : LTS ℓs ℓl ℓt) → (R : LTS.State lts → LTS.State lts → Set) → Set (ℓs ⊔ ℓl ⊔ ℓt)
IsSim lts R
  = (p q : State)
  → R p q
  → (l : Label)
  → (∀ p' → p -[ l ]-> p' → Σ[ q' ∈ State ] (q -[ l ]-> q'))
  where open LTS lts
  
IsBisimulation : (lts : LTS ℓs ℓl ℓt) → (R : LTS.State lts → LTS.State lts → Set) → Set (ℓs ⊔ ℓl ⊔ ℓt)
IsBisimulation lts R = IsSim lts R × IsSim lts (flip R)

IsBisimilarity :  (lts : LTS ℓs ℓl ℓt) → (_~_ : LTS.State lts → LTS.State lts → Set) → Set (suc zero ⊔ ℓs ⊔ ℓl ⊔ ℓt)
IsBisimilarity lts _~_
  = ∀ (p q : State)
  → ((p ~ q) ⇔ (Σ[ R ∈ (State → State → Set) ] (IsBisimulation lts R)))
  where open LTS lts

