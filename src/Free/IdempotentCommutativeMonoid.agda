open import Algebra.Structures.Propositional
module Free.IdempotentCommutativeMonoid
  {X : Set} {_≈_ : X → X → Set} {_<_ : X → X → Set}
  (<-STO : IsPropStrictTotalOrder _≈_ _<_)
  where

open import Free.IdempotentCommutativeMonoid.Base <-STO public
open import Free.IdempotentCommutativeMonoid.Properties <-STO public
