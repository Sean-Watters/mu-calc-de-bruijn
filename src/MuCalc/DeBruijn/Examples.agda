module MuCalc.DeBruijn.Examples where

open import MuCalc.DeBruijn.Base
open import MuCalc.DeBruijn.Latex
open import Data.Nat
open import Data.Fin
open import Data.String
open import Function

At = ℕ


ex1 : μML At 0
ex1 = μ (lit 0 ∨ ◆ (var zero))

ex2 : μML At 0
ex2 = ν (μ (◆ (var zero) ∨ (lit 0 ∧ ◆ (var (suc zero)))))

_ = {! toTeX $ expand (λ ()) ex2 !}
