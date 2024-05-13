module Relation.Binary.Isomorphism where

open import Function
open import Relation.Binary.PropositionalEquality

record _≃_ {n} (A B : Set n) : Set n where
  constructor MkIso
  field
    to : A → B
    from : B → A
    from-to : ∀ a → a ≡ from (to a)
    to-from  : ∀ b → b ≡ to (from b)

  to-inj : {x y : A} → to x ≡ to y → x ≡ y
  to-inj {x} {y} p = trans (from-to x) (trans (cong from p) (sym $ from-to y))

  from-inj : {x y : B} → from x ≡ from y → x ≡ y
  from-inj {x} {y} p = trans (to-from x) (trans (cong to p) (sym $ to-from y))
open _≃_ public

≃-sym : ∀ {n} {A B : Set n} → A ≃ B → B ≃ A
to (≃-sym iso) = from iso
from (≃-sym iso) = to iso
from-to (≃-sym iso) = to-from iso
to-from (≃-sym iso) = from-to iso

≃-refl : ∀ {n} {A : Set n} → A ≃ A
to ≃-refl = id
from ≃-refl = id
from-to ≃-refl _ = refl
to-from ≃-refl _ = refl

≃-trans : ∀ {n} {A B C : Set n} → A ≃ B → B ≃ C → A ≃ C
to (≃-trans p q) = to q ∘ to p
from (≃-trans p q) = from p ∘ from q
from-to (≃-trans p q) a = trans (from-to p a) (cong (from p) (from-to q (to p a)))
to-from (≃-trans p q) a = trans (to-from q a) (cong (to q) (to-from p (from q a)))


_≃ᵢ_ : ∀ {n} {I : Set n} → (I → Set n) → (I → Set n) → Set n
P ≃ᵢ Q = ∀ {i} → P i ≃ Q i
