{-# OPTIONS --safe #-}

module Data.Thinning.Properties where

open import Data.Nat
open import Data.Fin as F using ()
open import Relation.Binary.PropositionalEquality

open import Data.Thinning.Base as Th

open Th.Fin

-- Thinnings from 0 are propositions.
thin0-prop : ∀ {i} → (θ1 θ2 : Thin 0 i) → θ1 ≡ θ2
thin0-prop end end = refl
thin0-prop (pad θ1) (pad θ2) = cong pad (thin0-prop θ1 θ2)

-- The isomorphism with Fin.
from-to : ∀ {i} (x : Thin 1 i) → x ≡ finIsoFrom (finIsoTo x)
from-to (inj x) = cong inj (thin0-prop x zeros)
from-to (pad x) = cong pad (from-to x)

to-from : ∀ {i} (x : F.Fin i) → x ≡ finIsoTo (finIsoFrom x)
to-from F.zero = refl
to-from (F.suc x) = cong F.suc (to-from x)
