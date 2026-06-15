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

IsBisimulation : (lts : LTS ℓs ℓl ℓt) → (R : LTS.State lts → LTS.State lts → Set) → Set (ℓs ⊔ ℓl ⊔ ℓt)
IsBisimulation lts R
  = {p q : State}
  → R p q
  → (l : Label)
  → (∀ {p'} → p -[ l ]-> p' → Σ[ q' ∈ State ] (q -[ l ]-> q') × (R p' q'))
  × (∀ {q'} → q -[ l ]-> q' → Σ[ p' ∈ State ] (p -[ l ]-> p') × (R p' q'))
  where open LTS lts
  
IsBisimilarity :  (lts : LTS ℓs ℓl ℓt) → (_~_ : LTS.State lts → LTS.State lts → Set) → Set (suc zero ⊔ ℓs ⊔ ℓl ⊔ ℓt)
IsBisimilarity lts _~_
  = ∀ (p q : State)
  → ((p ~ q) ⇔ (Σ[ R ∈ (State → State → Set) ] (IsBisimulation lts R) × R p q))
  where open LTS lts

