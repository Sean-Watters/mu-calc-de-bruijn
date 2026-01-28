
module Petri.Net.Poly where

open import Level using () renaming (zero to 0ℓ)
open import Data.Unit
open import Data.Product

open import ContainerSyntax.Base
open import ContainerSyntax.Morphism
open import ContainerSyntax.Semantics

-- Abstracting away the typed tokens to a single polynomial data structure at each place and replacing expressions with containers.
-- Categorically, this /should/ be `FQ -> Poly`
record PolyCPN : Set₁ where

  -- Basic data
  field
    Place : Set
    Transition : Set

    -- Every transition has some source and target arcs, connecting it to some places.
    Source Target : Transition → Place → `Set`

    -- Each place gets a type of data that it can store...
    Colour : Place → `Set`

  -- The full input data to a transition is the product of all of the data at its source places.
  InputData : Transition → `Set`
  InputData t = `Σ` Place (λ p → Source t p `×` Colour p)

  -- And likewise for the output data.
  OutputData : Transition → `Set`
  OutputData t = `Σ` Place (λ p → Target t p `×` Colour p)

  -- In this setting, a marking is just an assignment of typed data to each
  -- if we want multiple "coloured tokens", that has to be internalised in our
  -- choice of `Colour`.
  Marking : Set
  Marking = ∀ (p : Place) → ⟦ Colour p ⟧ []

  -- Inscriptions
  field
    -- The transition tells us how to transform data at its source places into data at
    -- its target places, but we also have to update the source data.
    TransformInputs : (t : Transition) → (InputData t ⇒ (InputData t `×` OutputData t))

--   IsFiring : Marking → Transition → Marking → Set
--   IsFiring m₀ t m₁ = Guard t m₀ -- if we are allowed to fire t at m₀...
--                    → {!...then firing t at m₀ transforms the data at the places such that we end up at m₁!}

--   -- field
--     -- Source? : ∀ t p → Dec (Source t p)
--     -- Target? : ∀ t p → Dec (Target t p)
--     -- Guard? : ∀ {t} i o → Dec (Guard t i o)

-- -- TODO: The guards get baked into one of the other fields via proof relevance (a span!), but
-- -- I forget which or how. Source/Target? Or was it TransformInputs?
