{-# OPTIONS --guardedness #-}

module Codata.AltCoList where

open import Level using (Level; _⊔_)

private variable
  ℓx ℓy ℓp : Level

-- AltCoList X Y  ≈  "Alternating colists of X's and Y's, which if they terminate, always end in an X"
-- ε, X, XYX, XYXYX, ...
--
-- AltCoList X Y = 1 + νA. X * (1 + (Y * A))
--
-- Beware of dragons?
-- There's no quantifier alternation here, so I don't *think* there should be any
-- need to worry about Agda doing μ/ν inversion in the background, but it bears
-- being mindful about since we do have a coinductive record (ACLX) nested inside
-- inductive data (AltCoList). Need to be sure that the ν doesn't bubble too far out.
-- Note that `νA. 1 + (X * (1 + (Y * A)))` has different semantics; it allows termination after a Y.

mutual
  record ACLX (X : Set ℓx) (Y : Set ℓy) : Set (ℓx ⊔ ℓy) where
    constructor _∷_
    coinductive
    field
      head : X
      tail : ACLY X Y

  data ACLY (X : Set ℓx) (Y : Set ℓy) : Set (ℓx ⊔ ℓy) where
    [] : ACLY X Y
    _∷_ : Y → ACLX X Y → ACLY X Y

data AltCoList (X : Set ℓx) (Y : Set ℓy) : Set (ℓx ⊔ ℓy) where
  [] : AltCoList X Y
  ne : ACLX X Y → AltCoList X Y


------------------------
-- Predicate Liftings --
------------------------

-- The idea is that we have some system with states X and events Y that can fire, changing the state.
-- We can define a predicate expressing "when event y fires in state x0, we arrive in state x1".
-- Such a predicate has type `P : X → Y → X → Set`.
--
-- We want to now lift such predicates to alternating co-lists of X's and Y's, representing a sequence
-- of events firing, each one taking us to a new state.
-- Such a lifting will itself be a co-list of P's, with the initial state of the next P being the final
-- state of the previous.

-- NB: This is the pure inductive version that can only witness correctness for finite prefixes
-- of the alternating co-list.
-- The proper coinductive lifting is the next step.
data Lift {X : Set ℓx} {Y : Set ℓy} (P : X → Y → X → Set ℓp) : AltCoList X Y → Set (ℓx ⊔ ℓy ⊔ ℓp) where
  [] : Lift P []
  [x] : {x : X} → Lift P (ne (x ∷ []))
  _∷_ : {x₀ x₁ : X} {y : Y} {ys : ACLY X Y}
      → P x₀ y x₁
      → Lift P (ne (x₁ ∷ ys))
      → Lift P (ne (x₀ ∷ (y ∷ (x₁ ∷ ys))))
