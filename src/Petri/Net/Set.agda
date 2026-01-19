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

    -- ⟦_⟧v : Var → ColourUniverse

    -- The language which the guard functions are expressed in
    GuardExpr : (Var : Set) → Set

    -- Each transition is assigned an expression for whether it's enabled or not, which
    -- can make use of whatever structure the colours have
    guard : Transition → GuardExpr Var

    -- Traditionally, every guard expression is valued in booleans.
    -- For us, that means it's a decidable prop.
    ⟦_⟧g : GuardExpr Var → Set
    ⟦_⟧g? : ∀ g → Dec ⟦ g ⟧g

    -- -- Is the variable used in this expression?
    -- InGuard : Var → GuardExpr Var → Set


  field
    -- The language of well-typed arc expressions
    ArcExpr : (Var : Set) → ColourUniverse → Set

    -- Likewise, each arc is assigned an expression saying what it does
    source-expr : ∀ {t p} → Source t p → ArcExpr Var (Colour p)
    target-expr : ∀ {t p} → Target t p → ArcExpr Var (Colour p)

    -- Arc expressions are valued in colours
    ⟦_⟧a : ∀ {Col} → ArcExpr Var Col → ⟦ Col ⟧c


  -- A marking for a net is a list of typed tokens assigned to each place.
  -- This should really be a multiset instead, but until I see evidence that we actually
  -- need the equational theory of multisets, lists will suffice.
  Marking : Set
  Marking = ∀ (p : Place) → List ⟦ Colour p ⟧c

  -- -- A binding of a transition t is a function that maps each variable used in that t's
  -- -- guard to an element of that variable's colour set.
  -- Binding : Transition → Set
  -- Binding t = ∀ {v} → InGuard v (guard t) → ⟦ ⟦ v ⟧v ⟧c
  -- -- I think this is irrelevant to this formulation, since vars are necessarily
  -- given meaning by ⟦_⟧a and ⟦_⟧g....though they may not agree....hmmmm.....

  --
  IsEnabled : (t : Transition) → Set
  IsEnabled t = ⟦ guard t ⟧g
              × {!∀ {p} → source-expr {t} {p}!}



-- Abstracting away the tokens, and replacing expressions with directly embedded agda functions
-- and predicates.
record SemanticCPN : Set₁ where

  -- Basic data
  field
    Place : Set
    Transition : Set

    -- Every transition has some source and target arcs, connecting it to some places.
    Source Target : Transition → Place → Set

    -- Each place gets a type of data that it can store...
    Colour : Place → Set

  -- The full input data to a transition is the product of all of the data at its source places.
  InputData : Transition → Set
  InputData t = Σ[ p ∈ Place ] (Source t p) × Colour p

  -- And likewise for the output data.
  OutputData : Transition → Set
  OutputData t = Σ[ p ∈ Place ] (Target t p) × Colour p

  -- Inscriptions
  field
    -- The transition tells us how to transform data at its source places into data at
    -- its target places, but we also have to update the source data...
    TransformInputs : (t : Transition) → {!Fuck, it's a lens, isn't it!}

    -- Every transition gets a decidable "guard" which decides if the
    -- transition is allowed to be enabled, based on the data at its
    -- source and target places.
    Guard : (t : Transition) → InputData t → OutputData t → Set

  -- In this setting, a marking is just an assignment of typed data to each place.
  Marking : Set
  Marking = ∀ p → Colour p

  IsFiring : Marking → Transition → Marking → Set
  IsFiring m₀ t m₁ = ∀ {sp tp} (sa : Source t sp) (ta : Target t tp)
                   → Guard t (sp , sa , m₀ sp) (tp , ta , m₀ tp) -- if we are allowed to fire t at m₀...
                   → {!...then firing t at m₀ transforms the data at the places such that we end up at m₁!}

  -- Decidability stuff
  field
    Source? : ∀ t p → Dec (Source t p)
    Target? : ∀ t p → Dec (Target t p)
    Guard? : ∀ {t} i o → Dec (Guard t i o)
