{-# OPTIONS --safe #-}
module Data.Fin.Renaming where

open import Data.Nat
open import Data.Fin
open import Data.Thinning hiding (id)
open import Relation.Binary.PropositionalEquality
open import Function

----------
-- Core --
----------

-- Renamings are maps of variables
Rename : ℕ → ℕ → Set
Rename n m = Fin n → Fin m

-- Renaming extension
ext : ∀ {n m} → Rename n m → Rename (suc n) (suc m)
ext ρ zero = zero
ext ρ (suc x) = suc (ρ x)

-------------------------
-- Properties of `ext` --
-------------------------

ext-id : ∀ {i} → ext {i} id ≗ id
ext-id zero = refl
ext-id (suc x) = refl

ext-cong : ∀ {n m} {ρ1 ρ2 : Fin n → Fin m} → ρ1 ≗ ρ2 → ext ρ1 ≗ ext ρ2
ext-cong eq zero = refl
ext-cong eq (suc x) = cong suc (eq x)

ext-eq : ∀ {i j} {ρ ρ' : Rename i j}
       → ρ ≗ ρ'
       → ext ρ ≗ ext ρ'
ext-eq eq zero = refl
ext-eq eq (suc x) = cong suc (eq x)

ext-fusion : ∀ {i j k} {ρ1 : Rename j k} {ρ2 : Rename i j} {ρ3 : Rename i k}
           → ρ1 ∘ ρ2 ≗ ρ3
           → (ext ρ1) ∘ (ext ρ2) ≗ ext ρ3
ext-fusion eq zero = refl
ext-fusion eq (suc x) = cong suc (eq x)

ext∘embed : ∀ {i j} → (θ : Thin i j) → ext (embed θ) ≗ embed (inj θ)
ext∘embed θ zero = refl
ext∘embed θ (suc x) = refl

embed-ext : ∀ {i j} {θ : Thin i j} {f : Rename i j} → embed θ ≗ f → embed (inj θ) ≗ ext f
embed-ext p zero = refl
embed-ext p (suc x) = cong suc (p x)

-- TODO: making renaming generic on syntaxes with binding
