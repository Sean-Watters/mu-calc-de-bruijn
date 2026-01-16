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

  field
    -- A global set of variables to be used in guard and arc expressions.
    -- This is the way Jensen & Kristensen cook it, and it might be ergonomic
    -- for building nets, but maybe not the most neat way from a theory pov.
    Var : Set

    -- The language which the guard functions are expressed in
    GuardExpr : (Var : Set) → Set

    -- Each transition is assigned an expression for whether it's enabled or not, which
    -- can make use of whatever structure the colours have
    guard : Transition → GuardExpr Var

    -- Every guard expression is valued in booleans
    ⟦_⟧g : GuardExpr Var → Bool


  field
    -- The language of well-typed arc expressions
    ArcExpr : (Var : Set) → ColourUniverse → Set

    -- Likewise, each arc is assigned an expression saying what it does
    source-expr : ∀ {t p} → Source t p → ArcExpr Var (Colour p)
    target-expr : ∀ {t p} → Target t p → ArcExpr Var (Colour p)

    -- Arc expressions are valued in colours
    ⟦_⟧a : ∀ {Col} → ArcExpr Var Col → ⟦ Col ⟧c


  -- A marking for a net is an assignment of typed data to each place???
  -- TODO - is that right?
  Marking : Set
  Marking = ∀ (p : Place) → ⟦ Colour p ⟧c


  {-
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

  -}
