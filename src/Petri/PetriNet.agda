{-# OPTIONS --with-K #-}
module Petri.PetriNet where

open import Data.Product
open import Data.Nat as ℕ
open import Data.Fin
open import Data.List hiding (unfold)
open import Relation.Binary.PropositionalEquality

open import Relation.Unary.Finiteness.WithK
open import Data.Kripke
open Kripke

record PetriNet : Set₁ where
  field
    -- A finite set of places (circles)
    Place : Set
    Place-finite : Enumerated Place

    -- A finite set of transitions (boxes)
    Transition : Set
    Transition-finite : Enumerated Transition

  -- A marking is a map which tells you how many tokens are at each place.
  -- todo: generalise to arbitrary (X : Set)? Could parameterise, or have it be another family on places
  -- if we do that, we need X to be a monoid...at minimum...
  Marking = Place → ℕ

  field
    -- Each transition has a source and target marking that says how many tokens it consumes from each
    -- input and output place (respectively) when it fires. This can also be interpreted as the number
    -- of incoming and outgoing arcs; in this semantics, a transition firing moves exactly 1 token along each arc.
    source target : Transition → Marking -- source τ p ≈ the number of arcs from p to τ

  _M≤_ : Marking → Marking → Set
  m M≤ m' = ∀ p → m p ℕ.≤ m' p

  IsEnabled : Marking → Transition → Set
  IsEnabled m t = source t M≤ m

  -- When a transition "fires", it moves some tokens from the input place to the output place.
  -- W
  fire : Marking → Transition → Marking
  fire m t = {! m - source t + target t!}

  -- m is a possible next marking if there is some transition t, such that when t fires,
  -- m is indeed the result.
  IsSuccessor : Marking → Marking → Set
  -- IsSuccessor m m' = Σ[ t ∈ Transition ] {!(fire m t ≗ m')!} -- todo: this doesn't account for transitions firing in parallel
  IsSuccessor m m' = Σ[ ts ∈ List Transition ] {!fire each transition in the list consecutively (it's commutative so theres a unique result), then the result should be equal to m'!}

  -- m' is a reachable marking if there is a finite chain of transitions firing takes us there
  IsReachable : Marking → Marking → Set
  IsReachable m m' = {!Reflexive transitive closure of IsSuccessor!}

record ColouredPetriNet : Set₁ where
  field
    net : PetriNet

  open PetriNet net

  field
    -- Every place gets a set of colours/types that the tokens there can have
    Colour : Place → Set

  MarkingColour : Marking → Set
  MarkingColour m = ∀ p → Fin (m p) → Colour p

  field
    colour-map : ∀ (t : Transition) → MarkingColour (source t) → MarkingColour (target t)


---------------------------------------------------------------------------------------------------------

open PetriNet

unfold : PetriNet → (Kripke {!!})
unfold P .S = Marking P
unfold P ._~>_ = IsSuccessor P
unfold P .V x m = {!!}
