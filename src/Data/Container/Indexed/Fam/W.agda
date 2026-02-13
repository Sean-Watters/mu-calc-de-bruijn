{-# OPTIONS --safe #-}
module Data.Container.Indexed.Fam.W where

open import Data.Product using (_,_; -,_)
open import Function

open import Data.Container.Indexed.Fam.Base
open import Data.Container.Indexed.Fam.Morphism
open import Data.Container.Indexed.Fam.Relation.Unary.All
open Container

private variable
  I J : Set

-- Indexed W-types. AKA how to generate families of inductive data types
-- from indexed containers.
-- W-types are trees with node arity given by the set of shapes, and
data W {J : Set} (C : Container J J) : J → Set where
  sup : ∀ {j} → ⟦ C ⟧ (W C) j → W C j


head : {C : Container J J}
    → ∀ {j} → W C j → Shape C j
head (sup (s , f)) = s

tail : {C : Container J J}
    → ∀ {j} → (x : W C j) → Position C (head x) j → W C j
tail (sup (s , f)) = f

map : ∀ {C D : Container J J}
    → C ⇒ D
    → (∀ {j} → W C j → W D j)
map m (sup (s , f)) = sup (⟪ m ⟫ (s , λ p → map m (f p)))


module _ {C : Container J J}
         (P : ∀ {j} → W C j → Set)
         (algebra : ∀ {j} → {t : ⟦ C ⟧ (W C) j} → □ C P t → P (sup t)) where

  induction : ∀ {j} → (w : W C j) → P w
  induction {j} (sup (s , f)) = algebra (all ((induction ∘ f) _))

module _ {C : Container J J}
         (P : J → Set)
         (algebra : ∀ {j} → ⟦ C ⟧ P j → P j) where

  fold : ∀ {j} → W C j → P j
  fold = induction (λ {j} _ → P j) (λ x → algebra (-, λ p → □.proof x {p = p}))
