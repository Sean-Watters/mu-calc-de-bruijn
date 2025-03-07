{-# OPTIONS --sized-types #-}

open import Data.Kripke
open import Data.Nat
module MuCalc.Metatheory (M : Kripke ℕ) where

open import Algebra.Structures.Propositional
open import Data.Container.Indexed.Fam renaming (⟦_⟧ to ⟦_⟧c)
open import Data.Nat.Properties
open import Data.Vec
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Function
open import Relation.Binary using ()
open import Relation.Binary.PropositionalEquality

private
  At = ℕ
  <-STO : IsPropStrictTotalOrder _≡_ _<_
  IsPropStrictTotalOrder.isSTO <-STO = <-isStrictTotalOrder
  IsPropStrictTotalOrder.≈-prop <-STO = ≡-irrelevant
  IsPropStrictTotalOrder.<-prop <-STO = <-irrelevant

open import MuCalc.Base renaming (⊤ to ⊤'; ⊥ to ⊥')
open import MuCalc.Proof.Kozen <-STO
open import MuCalc.Semantics.Container <-STO M

open Kripke
open Container

-- soundness : ∀ {n} {ϕ : μML At n} → ⊢ ϕ → (i : Vec (S M → Set) n) → (s : S M) → ⟦ ϕ ⟧ i s
-- soundness = ?
