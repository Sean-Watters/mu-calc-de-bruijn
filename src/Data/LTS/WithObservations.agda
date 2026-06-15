{-# OPTIONS --safe #-}
module Data.LTS.WithObservations where

open import Data.LTS.Core as Lts using (LTS)

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

-- LTS with observations
record LTSO : Set₁ where
  field
    lts : LTS
  open LTS lts public
  field
    X : Set
    Observe : State -> X

-- A bisimulation on the underlying LTS, plus the observations have to match
-- at bisimilar states.
IsBisimulation : (ltso : LTSO) → (R : (p q : LTSO.State ltso) → Set) → Set
IsBisimulation ltso R
  = Lts.IsBisimulation lts R
  × ((p q : State) → R p q → Observe p ≡ Observe q)
  where open LTSO ltso                    

-- Bisimilarity is exactly the same, except it uses the new notion of bisimulation.
IsBisimilarity :  (ltso : LTSO) → (_~_ : (p q : LTSO.State ltso) → Set) → Set₁
IsBisimilarity ltso _~_
  = ∀ (p q : State)
  → ((p ~ q) ⇔ (Σ[ R ∈ (State → State → Set) ] (IsBisimulation ltso R)))
  where open LTSO ltso


-- We can encode an LTSO as an LTS by expanding the state space according to the
-- observations; our new states are the fibers at the observations of the old ones.
LTSO→LTS : LTSO → LTS
LTSO→LTS ltso .LTS.State = Σ[ s ∈ State ] Σ[ x ∈ X ] (Observe s ≡ x)
  where open LTSO ltso
LTSO→LTS ltso .LTS.Label = Label
  where open LTSO ltso
LTSO→LTS ltso .LTS._-[_]->_ (p , x , eq1) l (q , y , eq2) = p -[ l  ]-> q
  where open LTSO ltso


LTSO→LTS-preserves-bisimulation : (ltso : LTSO)
                                → (R : (p q : LTSO.State ltso) → Set)
                                → IsBisimulation ltso R
                                → Lts.IsBisimulation (LTSO→LTS ltso) (λ p q → R (p .proj₁) (q .proj₁))
LTSO→LTS-preserves-bisimulation ltso R isbisim .proj₁ p q Rpq l p' p→p'
  = let q→q' = isbisim .proj₁ .proj₁ (p .proj₁) (q .proj₁) Rpq l (p' .proj₁) p→p'
    in (q→q' .proj₁ , {!!}) , q→q' .proj₂
LTSO→LTS-preserves-bisimulation ltso R isbisim .proj₂ = {!!}
