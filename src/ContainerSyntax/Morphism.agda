
module ContainerSyntax.Morphism where

open import ContainerSyntax.Type
open import ContainerSyntax.Semantics renaming (⟦_⟧ to ⟦_⟧ty)

open import Data.Empty
open import Data.Unit
open import Data.Sum renaming ([_,_] to join)
open import Data.Product
open import Data.Vec
open import Data.Fin hiding (join)
open import Data.Nat

open import Function

open import Data.Container.Indexed.Fam
open import Data.Container.Indexed.Fam.Morphism as Lens hiding (_⇒_)


-- Ok....
record _⇒_ {n : ℕ} (X Y : Ty n) : Set₁ where
  field


open _⇒_

-- -- TODO - implement lens semantics
-- AsLens : {n : ℕ} {X Y : Ty n} → X ⇒ Y → (AsCont X) Lens.⇒ (AsCont Y)
-- AsLens = {!!}

-- TODO - extension of that lens to a polymorphic function

-- TODO - directly implement function semantics

-- TODO - correctness proof - they coincide
