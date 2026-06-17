{-# OPTIONS --safe #-}
module Data.LTS.WithObservations where

open import Data.LTS.Core as Lts using (LTS)

open import Level
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Function
open import Relation.Binary.PropositionalEquality

private variable
  ℓs ℓl ℓt ℓx : Level

-- LTS with observations
record LTSO (ℓs ℓl ℓt ℓx : Level) : Set (suc (ℓs ⊔ ℓl ⊔ ℓt ⊔ ℓx)) where
  field
    lts : LTS ℓs ℓl ℓt
  open LTS lts public
  field
    Data : Set ℓx
    Observe : State -> Data

-- A bisimulation on the underlying LTS, plus the observations have to match
-- at bisimilar states.
record IsBisimulation (ltso : LTSO ℓs ℓl ℓt ℓx) (R : (p q : LTSO.State ltso) → Set) : Set (ℓs ⊔ ℓl ⊔ ℓt ⊔ ℓx) where
  open LTSO ltso                    
  field
    lts-bisim : Lts.IsBisimulation lts R
    eq-obervations : ({p q : State} → R p q → Observe p ≡ Observe q)

-- Bisimilarity is exactly the same, except it uses the new notion of bisimulation.
IsBisimilarity :  (ltso : LTSO ℓs ℓl ℓt ℓx) → (_~_ : (p q : LTSO.State ltso) → Set) → Set (suc zero ⊔ ℓs ⊔ ℓl ⊔ ℓt ⊔ ℓx)
IsBisimilarity ltso _~_
  = ∀ (p q : State)
  → ((p ~ q) → (Σ[ R ∈ (State → State → Set) ] (IsBisimulation ltso R) × R p q))
  × ((Σ[ R ∈ (State → State → Set) ] (IsBisimulation ltso R) × R p q) → (p ~ q))
  where open LTSO ltso


-- By adding Data to the state space, and adding a new "observe" label for transitions to Data,
-- we can encode (Data, Observe) in a normal LTS.

LTSO→LTS : LTSO ℓs ℓl 0ℓ 0ℓ → LTS ℓs ℓl 0ℓ
LTSO→LTS ltso .LTS.State = State ⊎ Data
  where open LTSO ltso
LTSO→LTS ltso .LTS.Label = Maybe Label -- `nothing` represents the "observation" transitions
  where open LTSO ltso
LTSO→LTS ltso .LTS._-[_]->_ (inj₁ s) (just l) (inj₁ t) = (s -[ l ]-> t) -- l-labelled transitions s→t are as usual
  where open LTSO ltso
LTSO→LTS ltso .LTS._-[_]->_ (inj₁ s) nothing (inj₂ x) =  Observe s ≡ x -- nothing-labelled transitions s→x are observation
  where open LTSO ltso
LTSO→LTS ltso .LTS._-[_]->_ _ _ _ = ⊥ -- there are no other transitions


-- LTSO→LTS-preserves-bisimulation : (ltso : LTSO ℓs ℓl 0ℓ 0ℓ)
--                                 → (R : (p q : LTSO.State ltso) → Set)
--                                 → IsBisimulation ltso R
--                                 → Lts.IsBisimulation (LTSO→LTS ltso) {!R!}
-- LTSO→LTS-preserves-bisimulation ltso R isbisim = {!!}

