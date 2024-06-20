
module MuCalc.DeBruijn.Syntax.Closure where

open import Algebra.Structures.Propositional
open import Data.Nat
open import Data.Fin
open import Data.Vec
open import MuCalc.DeBruijn.Base
open import MuCalc.DeBruijn.Guarded
open import Relation.Binary.PropositionalEquality

mutual
  data Guardedε (At : Set) {n : ℕ} (Γ : Vec ℕ n) : Set where
    var : (x : Fin n) → {{NonZero (lookup Γ x)}} → Guardedε At Γ
    μML₀ : (op : Op₀ At) → Guardedε At Γ
    μML₁ : (op : Op₁) → (ϕ : Guardedε At {n} ones) → Guardedε At Γ
    μML₂ : (op : Op₂) → (ϕ : Guardedε At (inc Γ)) → (ψ : Guardedε At (inc Γ)) → Guardedε At Γ
    μMLη : (op : Opη) → (ϕ : Guardedε At (0 ∷ inc Γ)) → Guardedε At Γ
    ε : {ϕ : Guardedε At Γ} → IsFP ϕ → Guardedε At Γ

  data IsFP {At : Set} {n : ℕ} {Γ : Vec ℕ n} : Guardedε At Γ → Set where
    fp : (op : Opη) (ϕ : Guardedε At (0 ∷ inc Γ)) → IsFP (μMLη op ϕ)

-- these are trivial but really annoying to do manually. ned some "deriving" metaprogram...
postulate _<ε_ : {At : Set} {n : ℕ} {Γ : Vec ℕ n} → (ϕ ψ : Guardedε At Γ) → Set
postulate <ε-STO : (At : Set) {n : ℕ} (Γ : Vec ℕ n) → IsPropStrictTotalOrder {Guardedε At Γ} _≡_ _<ε_

open import Data.FreshList.InductiveInductive
open import Free.IdempotentCommutativeMonoid.Base
open import Free.IdempotentCommutativeMonoid.Properties

subε : {At : Set} {n : ℕ} {Γ : Vec ℕ n}
    → (ϕ : Guardedε At Γ)
    → Fin n
    → Guardedε At Γ
    → Guardedε At Γ
subε = {!!}

unfoldε : {At : Set} {n : ℕ} {Γ : Vec ℕ n}
        → {ϕ' : Guardedε At Γ} (ϕ : IsFP ϕ') -- the original formula
        → Guardedε At Γ
unfoldε (fp op ϕ) = {!subε ϕ zero ?!} -- hmm...see below

-- We would like unfolding to be a simple instance of substitution,
-- but the scopes don't match. ϕ has an extra free variable compared to μϕ.
-- So a representation of syntax with binding where strengthening is free
-- would be good; because while ϕ has an extra free variable, ϕ[0/ψ] does *not*,
-- since we substitute away all its occurrences. So maybe co-de Bruijin is the way.
