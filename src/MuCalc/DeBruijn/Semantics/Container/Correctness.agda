{-# OPTIONS --sized-types #-}

open import Algebra.Structures.Propositional
open import Relation.Binary.PropositionalEquality
open import Data.Kripke

module MuCalc.DeBruijn.Semantics.Container.Correctness
  {At : Set}
  {_<A_ : At → At → Set}
  (<A-STO : IsPropStrictTotalOrder _≡_ _<A_)
  (Mo : Kripke At)
  where


open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional using (Extensionality) renaming (implicit-extensionality to exti)

open import Data.Fin using (Fin)
open import Data.Vec using (Vec; lookup)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Container.Indexed.Fam renaming (⟦_⟧ to ⟨⟦_⟧⟩)
open import Data.Container.Indexed.Fam.SizedTypes
open import Data.Container.Indexed.Fam.Correctness

open import Function
open import Relation.Nullary
open import Relation.Binary.Isomorphism
open import MuCalc.DeBruijn.Base renaming (⊤ to ⊤'; ⊥ to ⊥') hiding (¬)
open import MuCalc.DeBruijn.Semantics.Container <A-STO Mo

private
  open Kripke renaming (S to S'; _~>_ to R; V to V')
  S = S' Mo
  _~>_ = R Mo
  V = V' Mo
  open Container

module VarCorrect (ext : Extensionality 0ℓ 0ℓ) where
  var-correct : ∀ {n} (x : Fin n) (i : Vec (S → Set) n)
              → ⟦ var x ⟧ i ≃ᵢ lookup i x
  to (var-correct x i {s}) (_ , P) = P (refl , refl)
  from (var-correct x i {s}) X = _ , λ { {t , .x} (refl , refl) → X}
  from-to (var-correct x i {s}) (tt , P) = cong (tt ,_) (exti ext (λ { {t , y} → ext (λ { (refl , refl) → refl }) }))
  to-from (var-correct x i {s}) b = refl

module BoxCorrect where
  correct : ∀ {n} (s : S) (i : Vec (S → Set) n) (ϕ : μML At n)
          → ⟦ ■ ϕ ⟧ i s ≃ ((t : S) → s ~> t → ⟦ ϕ ⟧ i t )
  to (correct s i ϕ) (σ , Q) t sRt = σ (t , sRt) , λ x → Q (t , sRt , x)
  from (correct s i ϕ) σ = (λ { (t , sRt) → proj₁ (σ t sRt)}) , λ { (t , sRt , P) → proj₂ (σ t sRt) P}
  from-to (correct s i ϕ) a = refl
  to-from (correct s i ϕ) b = refl

module DiamondCorrect where
  correct : ∀ {n} {s : S} {i : Vec (S → Set) n} (ϕ : μML At n)
          → ⟦ ◆ ϕ ⟧ i s ≃ (Σ[ t ∈ S ] (s ~> t) × ⟦ ϕ ⟧ i t)
  to (correct ϕ) ((t , sRt , S) , P) = t , sRt , S , P
  from (correct ϕ) (t , sRt , S , P) = (t , sRt , S) , P
  from-to (correct ϕ) a = refl
  to-from (correct ϕ) b = refl

module AndCorrect (ext : Extensionality 0ℓ 0ℓ) where
  correct : ∀ {n} (s : S) (i : Vec (S → Set) n) (ϕ ψ : μML At n)
          → ⟦ ϕ ∧ ψ ⟧ i s ≃ (⟦ ϕ ⟧ i s × ⟦ ψ ⟧ i s)
  correct s i ϕ ψ = BinaryProduct.correct ext (interpret-vec i) (MkCont ϕ) (MkCont ψ)

module OrCorrect (ext : Extensionality 0ℓ 0ℓ) where
  correct : ∀ {n} (s : S) (i : Vec (S → Set) n) (ϕ ψ : μML At n)
          → ⟦ ϕ ∨ ψ ⟧ i s ≃ (⟦ ϕ ⟧ i s ⊎ ⟦ ψ ⟧ i s)
  correct s i ϕ ψ = BinarySum.correct ext (interpret-vec i) (MkCont ϕ) (MkCont ψ)


module TrueCorrect (ext : Extensionality 0ℓ 0ℓ) where
  correct : ∀ {n} (s : S) (i : Vec (S → Set) n)
          → ⟦ ⊤' ⟧ i s ≃ ⊤
  correct {n} s i = Constant.correct ext (const ⊤) (interpret-vec i) {s , {!!}}
