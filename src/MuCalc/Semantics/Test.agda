
{-# OPTIONS --sized-types #-}

-- The type-theoretic semantics of the modal mu calculus, realised by containers.
-- We chose Sized Types as the foundation for coinduction.
module MuCalc.Semantics.Test where

open import Algebra.Structures.Propositional
open import Relation.Binary.PropositionalEquality
open import Data.Kripke
open import Data.Bool
open import Data.Fin as F
open import Data.Unit using (tt) renaming (⊤ to 𝟙)
open import Data.Empty using () renaming (⊥ to 𝟘)
open import Data.Vec as V
open import MuCalc.Base

M2 : Kripke Bool
M2 .Kripke.S = 𝟙
M2 .Kripke._~>_ _ _ = 𝟙
M2 .Kripke.V false x₁ = 𝟘
M2 .Kripke.V true x₁ = 𝟙

open import MuCalc.Semantics.Container M2

ϕ : μML Bool 0
ϕ = μ (μML₂ or ⊤ (μML₂ and (μML₀ (at true)) (◆ (var zero))))

_ = {!⟦ ϕ ⟧ [] tt!}
