
module Data.Vec.Extras where

open import Data.Vec
open import Data.Vec.Relation.Binary.Pointwise.Inductive as Vec
open import Data.Nat
open import Data.Nat.Minus

pointwise-minus : ∀ {n} → (xs ys : Vec ℕ n)
                → (ps : Vec.Pointwise _≤_ xs ys)
                → Vec ℕ n
pointwise-minus [] [] [] = []
pointwise-minus (x ∷ xs) (y ∷ ys) (x≤y ∷ ps) = minus x≤y ∷ pointwise-minus xs ys ps
