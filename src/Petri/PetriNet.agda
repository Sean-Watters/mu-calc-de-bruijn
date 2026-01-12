{-# OPTIONS --with-K #-}
module Petri.PetriNet where

open import Data.Bool
open import Data.Product
open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕ
open import Data.Nat.Minus as ℕ using ()
open import Data.Fin
open import Data.List hiding (unfold; lookup)
open import Data.Vec as Vec
open import Data.Vec.Relation.Binary.Pointwise.Inductive as VecPw using (Pointwise)
open import Data.Vec.Extras as Vec
open import Relation.Binary.PropositionalEquality

open import Relation.Nullary
open import Data.Kripke
open Kripke

import Petri.Marking

record PetriNet : Set₁ where
  field
    -- A finite number of places (circles)
    Place : ℕ

    -- A finite number of transitions (boxes)
    Transition : ℕ

  module M = Petri.Marking Place
  open M

  field
    -- Each transition has a source and target marking that says how many tokens it consumes from each
    -- input and output place (respectively) when it fires. This can also be interpreted as the number
    -- of incoming and outgoing arcs; in this semantics, a transition firing moves exactly 1 token along each arc.
    source target : Vec Marking Transition -- source τ p ≈ the number of arcs from p to τ


  -- Transition is enabled in the marking if the marking has enough tokens in the right places to feed all the
  -- source arcs.
  IsEnabled : Marking → Fin Transition → Set
  IsEnabled m t = (lookup source t) M.≤ m

  -- Which is a decidable notion.
  isEnabled? : ∀ m t → Dec (IsEnabled m t)
  isEnabled? m t = (lookup source t) M.≤? m


  -- When a transition "fires", it moves some tokens from the input place to the output place.
  -- W
  fire : Marking → Fin Transition → Marking
  fire m t with isEnabled? m t
  ... | yes p = add-markings (subtract-markings {lookup source t} {m} p) (lookup target t) -- (t.source - m) + t.target
  ... | no ¬p = m
  --{! if IsEnabled m t then { subtract-source m t + target t }!}

  -- m is a possible next marking if there is some transition t, such that when t fires,
  -- m is indeed the result.
  IsSuccessor : Marking → Marking → Set
  -- IsSuccessor m m' = Σ[ t ∈ Transition ] {!(fire m t ≗ m')!} -- todo: this doesn't account for transitions firing in parallel
  IsSuccessor m m' = Σ[ ts ∈ List (Fin Transition) ] {!fire each transition in the list consecutively (it's commutative so theres a unique result), then the result should be equal to m'!}

  -- m' is a reachable marking if there is a finite chain of transitions firing takes us there
  IsReachable : Marking → Marking → Set
  IsReachable m m' = {!Reflexive transitive closure of IsSuccessor!}



record ColouredPetriNet : Set₁ where
  field
    net : PetriNet

  open PetriNet net

  field
    -- Every place gets a set of colours/types that the tokens there can have
    ColourP : Vec Set Place
    ColourT : Vec Set Transition
      --Place → Set

  MarkingColour : M.Marking → Set
  MarkingColour m = ∀ (p : Fin Place) → Vec (lookup ColourP p) (lookup m p)
    --∀ p → Fin (m p) → Colour p

  field
    colour-map : ∀ (t : Fin Transition) (c : lookup ColourT t) → MarkingColour (lookup source t) → MarkingColour (lookup target t)

  -- converting a coloured petri net to an ordinary petri net in a semantics-preserving way
  unfold : PetriNet
  unfold .PetriNet.Place = {!Place  ColourP!}
  unfold .PetriNet.Transition = {!!}
  unfold .PetriNet.source = {!!}
  unfold .PetriNet.target = {!!}

---------------------------------------------------------------------------------------------------------

record PetriNetAbstract : Set₁ where
  field
    Place : Set
    Transition : Set

  MarkingAbstract : Set
  MarkingAbstract = Place → ℕ

  field
    source target : Transition → MarkingAbstract -- source τ p ≈ the number of arcs from p to τ

  IsEnabled : MarkingAbstract → Transition → Set
  IsEnabled m t = ∀ p → source t p ℕ.≤ m p

  -- we can do (m₁ - m₀)  if  (m₀ ≤ m₁)
  minus : (m₁ m₀ : MarkingAbstract)
        → (∀ p → m₀ p ℕ.≤ m₁ p)
        → MarkingAbstract
  minus m₁ m₀ lt p = ℕ.minus (lt p)

  VerifyFire : Transition → MarkingAbstract → MarkingAbstract → Set
  VerifyFire t m₀ m₁ = Σ[ tE ∈ IsEnabled m₀ t ] (∀ p → m₁ p ℕ.≥ (minus m₀ (source t) tE p) ℕ.+ (target t p))

  --VerifyFiringSeq : codata structure alternating between (lists of transitions) (since they can fire in parallel) and markings

record ColouredPetriNetAbstract : Set₁ where
  field
    ColourP ColourT : Set

    Place : ColourP → Set
    Transition : ColourT → Set

  MarkingAbstract : ColourP → Set
  MarkingAbstract c = Place c → ℕ

  field
    source target : (cp : ColourP) (ct : ColourT) → Transition ct → MarkingAbstract cp


open PetriNet

unfold : PetriNet → (Kripke {!!})
unfold P .S = M.Marking P
unfold P ._~>_ = IsSuccessor P
unfold P .V x m = {!!}



