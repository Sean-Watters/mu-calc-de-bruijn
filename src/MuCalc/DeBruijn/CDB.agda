module MuCalc.DeBruijn.CDB where

open import MuCalc.DeBruijn.Base using (Op₀; Op₁; Op₂; Opη)
open import Data.Nat hiding (_≤_)
open import Data.Fin as F using (Fin)
open import Data.Bool using (Bool; true; false; T)

-- We only care about 1 kind for now, so scopes are nats and thinnings are just ≤
data _≤_ : ℕ → ℕ → Set where
  skip : ∀{i j} → i ≤ j → i ≤ suc j
  select : ∀ {i j} → i ≤ j → suc i ≤ suc j
  zero : 0 ≤ 0

data Cover (ov : Bool) : {i j : ℕ} → i ≤ j → j ≤ i → Set where
  done : Cover ov zero zero
  -- left : ∀ {i j} {θ : i ≤ j} {ϕ : j ≤ i} → Cover ov θ ϕ → Cover ov (select θ) (skip ϕ)
  -- right : ∀ {i j} {θ : i ≤ j} {ϕ : j ≤ i} → Cover ov θ ϕ → Cover ov (skip θ) (select ϕ)
  both : ∀ {i j} {θ : i ≤ j} {ϕ : j ≤ i} → {b : T ov} → Cover ov θ ϕ → Cover ov (select θ) (select ϕ)

-- data Cover : (k l m : ℕ) → Set where
--   done   : Cover 0 0 0
--   left   : ∀ {k l m} → Cover k l m → Cover (suc k)      l  (suc m)
--   right  : ∀ {k l m} → Cover k l m → Cover      k  (suc l) (suc m)
--   both   : ∀ {k l m} → Cover k l m → Cover (suc k) (suc l) (suc m)


-- data μML (At : Set) : ℕ → Set where
--   var : μML At 1
--   μML₀ : (op : Op₀ At) → μML At 0
--   μML₁ : ∀ {n} (op : Op₁) → (ϕ : μML At n) → μML At n
--   μML₂ : ∀ {k l m} → (op : Op₂) → Cover k l m → (ϕ : μML At k) → (ψ : μML At l) → μML At m
--   μMLη : ∀ {n} → (op : Opη) → (ϕ : μML At (suc n)) → μML At n

-- sub : ∀ {At : Set} {n m}
--     → μML At n
--     → Fin n
--     → μML At (suc m)
--     → μML At (n + m)
-- sub var x ψ = ψ
-- sub (μML₁ op ϕ) x ψ = μML₁ op (sub ϕ x ψ)
-- sub (μML₂ op (left C) ϕ ξ) x ψ = μML₂ op {!left C!} {!sub ϕ x ψ!} ξ
-- sub (μML₂ op (right C) ϕ ξ) x ψ = μML₂ op {!!} ϕ {!!}
-- sub (μML₂ op (both C) ϕ ξ) x ψ = μML₂ op {!!} {!!} {!!}
-- sub (μMLη op ϕ) x ψ = {!!}
