{-# OPTIONS --guardedness #-}

module Codata.AltCoList where

open import Level

-- AltCoList X Y  ≈  "Alternating colists of X's and Y's, which if they terminate, always end in an X"
-- ε, X, XYX, XYXYX, ...
--
-- AltCoList X Y = 1 + νA. X * (1 + (Y * A))
--
-- Beware of dragons?
-- There's no quantifier alternation here, so I don't *think* there should be any
-- need to worry about Agda doing μ/ν inversion in the background, but it bears
-- being mindful about since we do have a coinductive record (FiringSeqM) nested inside
-- inductive data (FiringSeq). Need to be sure that the ν doesn't bubble too far out.
-- Note that `νA. 1 + (X * (1 + (Y * A)))` is semantically distinct.

mutual
  record ACLX {ℓx ℓy : Level} (X : Set ℓx) (Y : Set ℓy) : Set (ℓx ⊔ ℓy) where
    coinductive
    field
      head : X
      tail : ACLY X Y

  data ACLY {ℓx ℓy : Level} (X : Set ℓx) (Y : Set ℓy) : Set (ℓx ⊔ ℓy) where
    [] : ACLY X Y
    _∷_ : Y → ACLX X Y → ACLY X Y

data AltCoList {ℓx ℓy : Level} (X : Set ℓx) (Y : Set ℓy) : Set (ℓx ⊔ ℓy) where
  [] : AltCoList X Y
  ne : ACLX X Y → AltCoList X Y
