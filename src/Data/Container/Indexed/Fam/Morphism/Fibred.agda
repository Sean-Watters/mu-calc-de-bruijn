
module Data.Container.Indexed.Fam.Morphism.Fibred where

open import Data.Container.Indexed.Fam.Base
open import Data.Product
open import Function

open Container

private variable
  I J : Set
  C D E : Container I J

-- A variant which is truly J-indexed, to play around with
-- "Fibred hom of indexed containers" -Timo
-- Possibly the wrong thing for now?
record IHom (C : Container I J) (D : Container I J) (j : J) : Set where
  constructor _▷_
  field
    fw : Shape C j → Shape D j
    bw : {s : Shape C j} → ∀ {i} → Position D (fw s) i → Position C s i

  ⟪_⟫ : {P : I → Set}
      → ⟦ C ⟧ P j → ⟦ D ⟧ P j
  ⟪_⟫ (s , p) = fw s , p ∘ bw
open IHom

⟨id⟩ : ∀ j → IHom C C j
⟨id⟩ {C = S ◁ P} j = id ▷ id

⟨comp⟩ : ∀ j → IHom C D j → IHom D E j → IHom C E j
⟨comp⟩ j f g = (g .fw ∘ f .fw) ▷ (f .bw ∘ g .bw)

