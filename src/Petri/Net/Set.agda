{-# OPTIONS --guardedness #-}

module Petri.Net.Set where

open import Codata.AltCoList
open import Data.Product
open import Data.List as List hiding (unfold; lookup)
open import Data.Fin
open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕ
open import Data.Nat.Minus as ℕ using ()
open import Function
open import Relation.Binary.PropositionalEquality


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


-- TODO: Something about this feels wrong; I'm not sure the colours are doing
-- the right thing. More clear to have sets of P's/T's and families of colours?

record ColouredPetriNet : Set₁ where
  field
    -- Places and transitions get colours, AKA types.
    -- (Or probably more accurately, descriptions of types)
    ColourP ColourT : Set

    -- We then have colour-indexed families of places and transitions
    -- (for each colour, a set of P's/T's which have that colour)
    Place : ColourP → Set
    Transition : ColourT → Set


  -- How many tokens (AKA variables of type `c`) are at each place?
  Marking : ColourP → Set
  Marking c = Place c → ℕ

  -- -- Wait, what is this doing??
  -- MarkingColour : ∀ {cp} → Marking cp → Set
  -- MarkingColour {cp} m = (p : Place cp) → Fin (m p) → ColourP


  Arc = {cp : ColourP} {ct : ColourT} → Transition ct → Marking cp

  field
    -- Arcs must be indexed by the colours of both the place and transition
    source target : Arc

    -- -- Wait, what is this doing?
    -- colour-map : ∀ {cp₀ ct cp₁} (t : Transition ct) → MarkingColour {cp₀} (source t) → MarkingColour {cp₁} (target t)

  ---------------------------

  IsEnabled : ∀ {cp ct} → Marking cp → Transition ct → Set
  IsEnabled {cp} {ct} m t = ∀ (p : Place cp) → source t p ℕ.≤ m p

  minus : ∀ {c} (m₁ m₀ : Marking c)
        → (∀ p → m₀ p ℕ.≤ m₁ p)
        → Marking c
  minus m₁ m₀ lt p = ℕ.minus (lt p)

  IsFiring : ∀ {cp₀ ct cp₁} → Marking cp₀ → Transition ct → Marking cp₁ → Set
  IsFiring {cp₀} {ct} {cp₁} m₀ t m₁
    = Σ[ tE ∈ IsEnabled m₀ t ]
      (∀ (p₀ : Place cp₀) (p₁ : Place cp₁) → m₁ p₁ ≡ (minus m₀ (source t) tE p₀) ℕ.+ (target t p₁))

  ---------------------------

  sum-arcs : Arc → List (Σ[ ct ∈ ColourT ] (Transition ct)) → {cp : ColourP} → Marking cp
  sum-arcs arc ts p = List.foldr ℕ._+_ 0 (List.map apply-arc ts) where
    apply-arc : Σ[ ct ∈ ColourT ] (Transition ct) → ℕ
    apply-arc (ct , t) = arc t p

  AllEnabled : ∀ {cp} → Marking cp → List (Σ[ ct ∈ ColourT ] (Transition ct)) → Set
  AllEnabled m ts = ∀ p → sum-arcs source ts p ℕ.≤ m p

  -- Morally should be Bags rather than lists, but since we're depending on finiteness/traversability, that's a pain.
  -- Fresh lists would be a very big dependency to bring in.
  IsParallelFiring : ∀ {cp₀ cp₁} → Marking cp₀ → List (Σ[ ct ∈ ColourT ] (Transition ct)) → Marking cp₁ → Set
  IsParallelFiring {cp₀} {cp₁} m₀ ts m₁
    = Σ[ tsE ∈ AllEnabled m₀ ts ]
      (∀ (p₀ : Place cp₀) (p₁ : Place cp₁) → m₁ p₁ ≡ (minus m₀ (sum-arcs source ts) tsE p₀ ℕ.+ (sum-arcs target ts p₁)))

  ---------------------------

  MarkingSeq : Set
  MarkingSeq = AltCoList (Σ[ cp ∈ ColourP ] (Marking cp)) (List (Σ[ ct ∈ ColourT ] (Transition ct)))

  IsFiringSeq : MarkingSeq → Set
  IsFiringSeq = Lift λ m₀ ts m₁ → IsParallelFiring (proj₂ m₀) ts (proj₂ m₁)
