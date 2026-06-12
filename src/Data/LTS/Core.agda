-- Labelled transition systems
module Data.LTS.Core where

open import Data.Product
open import Function

record LTS : Set₁ where
  field
    State : Set
    Label : Set
    _-[_]->_ : State -> Label -> State -> Set

IsSim : (lts : LTS) → (R : LTS.State lts → LTS.State lts → Set) → Set
IsSim lts R
  = (p q : State) (l : Label)
  → (∀ p' → p -[ l ]-> p' → Σ[ q' ∈ State ] (q -[ l ]-> q'))
  where open LTS lts
  
IsBisimulation : (lts : LTS) → (R : LTS.State lts → LTS.State lts → Set) → Set
IsBisimulation lts R = IsSim lts R × IsSim lts (flip R)

IsBisimilarity :  (lts : LTS) → (_~_ : LTS.State lts → LTS.State lts → Set) → Set₁
IsBisimilarity lts _~_
  = ∀ (p q : State)
  → ((p ~ q) ⇔ (Σ[ R ∈ (State → State → Set) ] (IsBisimulation lts R)))
  where open LTS lts

