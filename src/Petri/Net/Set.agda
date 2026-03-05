{-# OPTIONS --guardedness #-}

module Petri.Net.Set where

open import Codata.AltCoList
open import Data.Bool
open import Data.Product
open import Data.List as List hiding (unfold; lookup)
open import Data.Fin
open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕ
open import Data.Nat.Minus as ℕ using ()
open import Data.Sum
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary


------------------------------------------------

record PetriNet : Set₁ where
  field
    Place : Set
    Transition : Set

  Marking : Set
  Marking = Place → ℕ

  Arc : Set
  Arc = Transition → Marking

  field
    source target : Arc -- source τ p ≈ the number of arcs from p to τ

  ---------------------------

  IsEnabled : Marking → Transition → Set
  IsEnabled m t = ∀ p → source t p ℕ.≤ m p

  -- we can do (m₁ - m₀)  if  (m₀ ≤ m₁)
  minus : (m₁ m₀ : Marking)
        → (∀ p → m₀ p ℕ.≤ m₁ p)
        → Marking
  minus m₁ m₀ lt p = ℕ.minus (lt p)

  -- Can t fire at m₀, and if so, is m₁ the result?
  IsFiring : Marking → Transition → Marking → Set
  IsFiring m₀ t m₁
    = Σ[ tE ∈ IsEnabled m₀ t ]
      (∀ p → m₁ p ≡ (minus m₀ (source t) tE p) ℕ.+ (target t p))

  ---------------------------

  sum-arcs : Arc → List Transition → Marking
  sum-arcs arc ts p = List.foldr ℕ._+_ 0 (List.map ((_$ p) ∘ arc) ts)

  AllEnabled : Marking → List Transition → Set
  AllEnabled m ts = ∀ p → sum-arcs source ts p ℕ.≤ m p

  -- Morally should be Bags rather than lists, but since we're depending on finiteness/traversability, that's a pain.
  -- Fresh lists would be a very big dependency to bring in.
  IsParallelFiring : Marking → List Transition → Marking → Set
  IsParallelFiring m₀ ts m₁
    = Σ[ tsE ∈ AllEnabled m₀ ts ]
      (∀ p → m₁ p ≡ (minus m₀ (sum-arcs source ts) tsE p ℕ.+ (sum-arcs target ts p)))

  ---------------------------

  -- A firing sequence is an alternating co-list of markings interspersed by lists of transitions.
  -- It may or may not be an infinite sequence. If it terminates, it is guaranteed to terminate at a marking.
  -- A nonempty firing sequence denotes starting at some marking, firing some transitions in parallel, arriving
  -- at the next marking, and so on.
  MarkingSeq : Set
  MarkingSeq = AltCoList Marking (List Transition)

  -- A witness of correctness for a firing sequence is a co-list of witnesses that each Marking-Transitions-Marking
  -- triple is correct (ie, a co-list of VerifyFireParallel).
  IsFiringSeq : MarkingSeq → Set
  IsFiringSeq = Lift IsParallelFiring


-------------------------------------------------------
-------------------------------------------------------


-- As in Jensen & Kristensen 2009
-- Non-heirarchical (AKA non modular), from Chatper 4.
-- Compared to the above, we add types to the places, guards to the transitions, and typed expressions to the arcs.
-- The concept of tokens are abstracted to "typed data".
record ColouredPetriNet : Set₁ where
  field
    -- Net structure
    Place : Set
    Transition : Set

  -- The arcs are proof-relevant relations between transitions and places (AKA spans).
  -- This allegedly bakes in the guards???
  Arc = Transition → Place → Set
  field
    Source : Arc
    Target : Arc

    -- A set of colour sets, and the decoding function that inteprets these as
    -- actual Agda types.
    ColourUniverse : Set
    ⟦_⟧c : ColourUniverse → Set

    -- Each place is assigned a colouring set for its tokens
    Colour : Place → ColourUniverse

    -- NB: Doing colours this way was a design choice. We could have just had
    -- `Colour : Place → Set` and deleted `ColourUniverse` and `⟦_⟧`, but imo
    -- it's neater this way. Separates the matter of what colour sets are allowed
    -- from the assignment of colour sets to places.

  -- A marking for a net is a lump of typed data assigned to each place.
  Marking : Set
  Marking = ∀ (p : Place) → ⟦ Colour p ⟧c

  --
  IsEnabled : Marking → Transition → Set
  IsEnabled m t = ∀ p → Source t p ⊎ Target t p → {!m p!}
