{-# OPTIONS --sized-types #-}

open import Data.Product

-- The type-theoretic semantics of the modal mu calculus, realised by containers.
-- We chose Sized Types as the foundation for coinduction.
module MuCalc.Semantics.ContainerCoalg
  {F : Set → Set}
  (At : Set)
  (S : Set)
  (η : S → F At × F S)
  where

open import Data.Fin using (Fin; _≟_) renaming (zero to fzero; suc to fsuc)
open import Data.Vec using (Vec; lookup)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Container.Indexed.Fam renaming (⟦_⟧ to ⟨⟦_⟧⟩)
open import Data.Container.Indexed.Fam.SizedTypes
open import Data.Container.Indexed.Fam.Correctness

open import Function
open import Relation.Nullary
open import Relation.Binary.Isomorphism
open import Relation.Binary.PropositionalEquality
open import MuCalc.Base renaming (⊤ to ⊤'; ⊥ to ⊥') hiding (lookup)

private
  open Container
------------------------------------------------------------------------------

dist-fin : ∀ {n} → (S × Fin n) ⊎ S → S × Fin (suc n)
dist-fin {n} (inj₁ (s , m)) = s , fsuc m
dist-fin {n} (inj₂ s) = s , fzero


MkCont : {n : ℕ} → μML At n → Container (S × Fin n) S
MkCont {n} (var x) = (const ⊤) ◃ λ { {t} _ (s , y) → s ≡ t × x ≡ y}
MkCont ⊤' = ⟨const⟩ (const ⊤)
MkCont ⊥' = ⟨const⟩ (const ⊥)
MkCont (μML₀ (at x)) = ⟨const⟩ (V x)
MkCont (μML₀ (¬at x)) = ⟨const⟩ (λ s → ¬ (V x s))
MkCont (■ ϕ) = ?
MkCont (◆ ϕ) = ?
MkCont (ϕ ∧ ψ) = MkCont ϕ ⟨×⟩ MkCont ψ
MkCont (ϕ ∨ ψ) = MkCont ϕ ⟨+⟩ MkCont ψ
MkCont (μ ϕ) = ⟨μ⟩ (⟨map⟩ dist-fin (MkCont ϕ))
MkCont (ν ϕ) = ⟨ν⟩ (⟨map⟩ dist-fin (MkCont ϕ))


⟦_⟧ : ∀ {n} → μML At n → Vec (S → Set) n → S → Set
⟦_⟧ {n} ϕ i = ⟨⟦ MkCont ϕ ⟧⟩ (interpret-vec i)
