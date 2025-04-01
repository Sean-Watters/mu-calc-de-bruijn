{-# OPTIONS --safe #-}

module Data.Thinning.Base where

open import Data.Nat as N hiding (zero; suc; _+_)
open import Data.Fin as F using ()
open import Data.Sum as Sum
open import Data.Product

----------------
-- Data Types --
----------------

data Thin : ℕ → ℕ → Set where
  end : Thin 0 0                                      -- ε
  inj : ∀ {i j} → Thin i j → Thin (N.suc i) (N.suc j) -- 1 ∷_
  pad : ∀ {i j} → Thin i j → Thin i (N.suc j)         -- 0 ∷_

----------------
-- Operations --
----------------

-- The identity thinning; all 1's.
id : ∀ i → Thin i i
id (N.zero) = end
id (N.suc i) = inj (id i)

-- The empty thinning; all 0's.
zeros : ∀ {i} → Thin 0 i
zeros {N.zero} = end
zeros {N.suc i} = pad zeros

-- Thinning composition
-- AKA injecting into larger scopes without incrementing
_⨾_ : ∀ {i j k} → Thin i j → Thin j k → Thin i k
θ1 ⨾ end = θ1
θ1 ⨾ pad θ2 = pad (θ1 ⨾ θ2)
pad θ1 ⨾ inj θ2 = pad (θ1 ⨾ θ2)
inj θ1 ⨾ inj θ2 = inj (θ1 ⨾ θ2)

-- Tensor product of thinnings
_⊗_ : ∀ {i j k l} →  Thin i k → Thin j l → Thin (i N.+ j) (k N.+ l)
end ⊗ σ = σ
inj θ ⊗ σ = inj (θ ⊗ σ)
pad θ ⊗ σ = pad (θ ⊗ σ)

-------------------
-- Special Cases --
-------------------

-- The successor thinning
inc : ∀ i → Thin i (N.suc i)
inc i = pad (id i)

-- The `k+` thinning; repeated application of `inc`
plusL : ∀ {i} k → Thin i (k N.+ i)
plusL {i} N.zero = (id i)
plusL {i} (N.suc k) = (inc i) ⨾ inj (plusL k)


---------
-- Fin --
---------

-- Turning a thinning into an actual embedding of variables
embed : {i j : ℕ} → Thin i j → F.Fin i → F.Fin j
embed (inj θ) F.zero = F.zero
embed (inj θ) (F.suc x) = F.suc (embed θ x)
embed (pad θ) x = F.suc (embed θ x)

module Fin where
  Fin = Thin 1

  pattern fzero {θ} = inj θ
  pattern fsuc x = pad x

  -- The special case of composition for Fin's tells us how to inject Fins into larger scopes
  inject : ∀ {i j} → Fin i → Thin i j → Fin j
  inject x θ = x ⨾ θ

  splitAt : ∀ i {j} → Fin (i N.+ j) → Fin i ⊎ Fin j
  splitAt N.zero x = inj₂ x
  splitAt (N.suc i) (fzero {x}) = inj₁ (fzero {zeros})
  splitAt (N.suc i) (fsuc x) = Sum.map₁ fsuc (splitAt i x)


  zero : ∀ {i} → Fin (N.suc i)
  zero = fzero {zeros}

  -- And we get the expected isomorphism (proofs in Data.Thinning.Properties)
  finIsoTo : ∀ {i} → Fin i → F.Fin i
  finIsoTo fzero = F.zero
  finIsoTo (fsuc x) = F.suc (finIsoTo x)

  finIsoFrom : ∀ {i} → F.Fin i → Fin i
  finIsoFrom F.zero = inj zeros
  finIsoFrom (F.suc x) = fsuc (finIsoFrom x)

