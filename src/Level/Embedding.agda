
-- The embedding functor from small sets into large sets
module Level.Embedding where

open import Level
open import Function
open import Relation.Binary.PropositionalEquality

private variable
  ℓ : Level

-- Specialising `Lift` to bumping up by just one level
↑_ : Set ℓ → Set (suc ℓ)
↑_ {ℓ = ℓ} = Lift (suc ℓ)

↑-map : {X Y : Set ℓ} → (X → Y) → (↑ X → ↑ Y)
↑-map f (lift x) = lift (f x)

↑-map-preserves-id : {X : Set ℓ} → ↑-map {X = X} id ≗ id
↑-map-preserves-id (lift x) = refl

↑-map-preserves-∘ : {X Y Z : Set ℓ} (g : Y → Z) (f : X → Y)
                  → ↑-map (g ∘ f) ≗ (↑-map g ∘ ↑-map f)
↑-map-preserves-∘ _ _ _ = refl
