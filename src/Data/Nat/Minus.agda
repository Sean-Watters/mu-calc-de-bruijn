
module Data.Nat.Minus where

open import Data.Nat

minus : {n m : ℕ} → n ≤ m → ℕ
minus {zero} {m} z≤n = m
minus {suc n} {suc m} (s≤s p) = minus p
