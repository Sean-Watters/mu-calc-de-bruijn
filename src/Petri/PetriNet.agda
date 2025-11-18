{-# OPTIONS --with-K #-}
module Petri.PetriNet where

open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Relation.Unary.Finiteness.WithK
open import Data.Kripke
open Kripke

record Net : Set₁ where
  field
    -- A finite set of places (circles)
    Place : Set
    Place-finite : Enumerated Place

    -- A finite set of transitions (boxes)
    Transition : Set
    Transition-finite : Enumerated Transition

    -- Arcs go from places to transitions (the "incoming" arcs of that transition),
    -- and from transitions to places (the "outgoing" arcs).
    ArcI : Place → Transition → Set -- "incoming"
    ArcO : Transition → Place → Set -- "outgoing"

    -- Every place gets a set of colours/types that the tokens there can have
    Colour : Place → Set

    -- Every transition needs to say how to map the colours of its input places to
    -- the colours of its output places
    colour-map : ∀ {p t p'} → ArcI p t → ArcO t p' → (Colour p → Colour p')

---------------------------------------------------------------------------------------------------------

-- Parameterised over a set of tokens
record PetriNet (Tok : Set) : Set₁ where
  constructor PNet

  -- There is a net, obviously.
  field
    net : Net
  open Net net

  -- A marking is an assignment of a place and colour to each individual token in the token set.
  Marking : Set
  Marking = Tok → Σ[ p ∈ Place ] (Colour p)

  -- The net also has a marking.
  field
    marking : Marking

  -- When a transition "fires", it moves some tokens from the input place to the output place,
  -- mapping the colours appropriately.
  fire : Transition → Marking
  fire t = {!individual token semantics here!}

  -- Given a new marking, we can replace the current marking in this net.
  update : Marking → PetriNet Tok
  update m = record
              { net = net
              ; marking = m
              }

  -- m is a possible next marking if there is some transition t, such that when t fires,
  -- m is indeed the result.
  IsSuccessor : Marking → Set
  IsSuccessor m = Σ[ t ∈ Transition ] (fire t ≗ m)

  -- m is a reachable marking if there is a finite chain of transitions firing takes us there
  IsReachable : Marking → Set
  IsReachable = {!Reflexive transitive closure of IsSuccessor!}
open PetriNet

---------------------------------------------------------------------------------------------------------

unfold : ∀ {Tok} → PetriNet Tok → (Kripke {!!})
unfold {Tok} P .S = Marking P
unfold {Tok} P ._~>_ m m' = IsSuccessor (update P m) m' -- is m' a successor in the net P with marking M?
unfold {Tok} P .V x m = {!what do the atoms do?!}
