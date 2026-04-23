module Data.Container.Indexed.Fam.Combinator.Correctness where


open import Level
open import Axiom.Extensionality.Propositional using (Extensionality) renaming (implicit-extensionality to exti)
open import Data.Container.Indexed.Fam.Base
open import Data.Container.Indexed.Fam.Combinator.Base
open import Data.Container.Indexed.Fam.Morphism
open import Data.Product as Σ hiding (curry; uncurry)
open import Data.Empty
open import Data.Sum
open import Data.Unit
open import Function
open import Relation.Nullary using (¬_)
open import Relation.Binary.Isomorphism
open import Relation.Binary.PropositionalEquality hiding (J; [_])

open Container

private
  variable
    I J : Set

-- The meaning of the identity container is the identity function
module Identity (ext : Extensionality 0ℓ 0ℓ) where
  correct : (X : J → Set) → ⟦ ⟨id⟩ ⟧ X ≃ᵢ id X
  to (correct X) (tt , f) = f refl
  from (correct X) x = tt , λ { refl → x }
  from-to (correct X) (tt , f) = cong (tt ,_) (exti ext (ext (λ { refl → refl})))
  to-from (correct X) b = refl

-- The meaning of a constant contianer is a constant function
module Constant (ext : Extensionality 0ℓ 0ℓ) where
  correct : (X Y : J → Set) → ⟦ ⟨const⟩ X ⟧ Y ≃ᵢ const X Y
  to (correct X Y) (x , _) = x
  from (correct X Y) x = x , λ {()}
  from-to (correct X Y) (x , _) = cong (x ,_) (exti ext (ext λ {()}))
  to-from (correct X Y) x = refl

-- In particular, the unit container is the unit
module Unit (ext : Extensionality 0ℓ 0ℓ) where
  correct : (Y : J → Set) (j : J) → ⟦ ⟨⊤⟩ ⟧ Y j ≃ ⊤
  correct Y j .to x = tt
  correct Y j .from _ = tt , λ ()
  correct Y j .from-to (tt , snd) = cong (tt ,_) (exti ext (ext (λ ())))
  correct Y j .to-from tt = refl

-- And the empty container is the empty type
module Empty (ext : Extensionality 0ℓ 0ℓ) where
  correct : (Y : J → Set) (j : J) → ⟦ ⟨⊥⟩ ⟧ Y j ≃ ⊥
  correct Y j .to (() , snd)
  correct Y j .from ()
  correct Y j .from-to = λ ()
  correct Y j .to-from = λ ()


-- The meaning of a product of containers is the product of their
-- meanings.
module BinaryProduct (ext : Extensionality 0ℓ 0ℓ) where
  correct : (X : I → Set) → (C D : Container I J)
          → ⟦ C ⟨×⟩ D ⟧ X ≃ᵢ (λ j → ⟦ C ⟧ X j × ⟦ D ⟧ X j)
  to (correct X C D) ((c , d) , f) = (c , f ∘ inj₁) , (d , f ∘ inj₂)
  from (correct X C D) ((c , f) , (d , g)) = (c , d) , [ f , g ]
  from-to (correct X C D) (s , f) = cong (s ,_) (exti ext (ext [ (λ _ → refl) , (λ _ → refl) ]))
  to-from (correct X C D) ((c , f) , (d , g)) = cong₂ (λ x y → (c , x) , (d , y)) (exti ext (ext λ _ → refl)) (exti ext (ext λ _ → refl))

-- The meaning of an indexed product of containers is a pi type from
-- the indexing set into the meanings
module IndexedProduct (ext : Extensionality 0ℓ 0ℓ) where
  correct : (X : I → Set) → (Y : J → Set) → (C : {j : J} → Y j → Container I J)
          → ⟦ ⟨Π⟩ {X = Y} C ⟧ X ≃ᵢ λ j → ((y : Y j) → ⟦ C y ⟧ X j)
  to (correct X Y C) (s , f) y = s y , λ x → f (y , x)
  from (correct X Y C) f = (λ x → proj₁ (f x)) , (λ x → proj₂ (f (proj₁ x)) (proj₂ x))
  from-to (correct X Y C) (s , f) = cong (s ,_) (exti ext (ext λ _ → refl))
  to-from (correct X Y C) f = ext (λ _ → refl)

-- The meaning of a sum of containers is the sum of their
-- meanings.
module BinarySum (ext : Extensionality 0ℓ 0ℓ) where
  correct : (X : I → Set) → (C D : Container I J)
          → ⟦ C ⟨+⟩ D ⟧ X ≃ᵢ (λ j → ⟦ C ⟧ X j ⊎ ⟦ D ⟧ X j)
  to (correct X C D) (inj₁ c , f) = inj₁ (c , f)
  to (correct X C D) (inj₂ d , f) = inj₂ (d , f)
  from (correct X C D) (inj₁ (c , f)) = inj₁ c , f
  from (correct X C D) (inj₂ (d , f)) = inj₂ d , f
  from-to (correct X C D) (inj₁ x , snd) = refl
  from-to (correct X C D) (inj₂ y , snd) = refl
  to-from (correct X C D) (inj₁ x) = refl
  to-from (correct X C D) (inj₂ y) = refl

-- The meaning of an indexed sum of containers is a pair
-- of an index, and the meaning of its corresponding container
module IndexedSum (ext : Extensionality 0ℓ 0ℓ) where
  correct : (X : I → Set) → (Y : J → Set) → (C : {j : J} → Y j → Container I J)
          → ⟦ ⟨Σ⟩ Y C ⟧ X ≃ᵢ λ j → (Σ[ y ∈ Y j ] ⟦ C y ⟧ X j)
  to (correct X Y C) ((y , s) , f) = y , s , f
  from (correct X Y C) (y , s , f) = (y , s) , f
  from-to (correct X Y C) _ = refl
  to-from (correct X Y C) _ = refl


-- module LeastFixedPoint (ext : Extensionality 0ℓ 0ℓ) where
--   -- It's a fixpoint (F x ≈ F (F x))
--   correct : (X : I → Set) → {!!}
--   correct = {!!}
--
--   -- And it's the least one.
-- For correctness of greatest fixed point see ...Fam.SizedTypes.

-- Verifying the curry-adjunction of the internal hom.
-- Shouldn't there be some flavour of isomorphism between ⟦ C ⟨→⟩ D ⟧
-- and lenses? That doesn't quite type check, but why?
module Exponential where

  open BinaryProduct renaming (correct to ×-correct)

  curry : (X : I → Set) (C D E : Container I J)
        → (C ⟨×⟩ D) ⇒ E
        → C ⇒ (D ⟨→⟩ E)
  curry X C D E (fw ▷ bw) ._⇒_.fw = Σ.curry fw
  curry X C D E (fw ▷ bw) ._⇒_.bw f = {!f!} -- I think this makes it clears that the bw part of ⟨→⟩ is wrong

  uncurry : (X : I → Set) (C D E : Container I J)
          → C ⇒ (D ⟨→⟩ E)
          → (C ⟨×⟩ D) ⇒ E
  uncurry X C D E (fw ▷ bw) ._⇒_.fw = Σ.uncurry fw
  uncurry X C D E (fw ▷ bw) ._⇒_.bw p = {!bw!}
