
module ContainerSyntax.Term where

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.String
open import Data.Product
open import Data.Sum
open import Data.Fin

open import ContainerSyntax.Type

data Tm : {n : ℕ} → (Γ : Context n) → Ty n → Set₁ where
  `tt`   : ∀ {n} {Γ : Context n} → Tm Γ `1`

  `injL` : ∀ {n} {Γ : Context n} {L R : Ty n} → Tm Γ L → Tm Γ (L `+` R)
  `injR` : ∀ {n} {Γ : Context n} {L R : Ty n} → Tm Γ R → Tm Γ (L `+` R)

  _`,`_  : ∀ {n} {Γ : Context n} {L R : Ty n} → Tm Γ L → Tm Γ R → Tm Γ (L `×` R)

  _`,,`_ : ∀ {n} {Γ : Context n} {X : Set} {P : X → Ty n} → (x : X) → Tm Γ (P x) → Tm Γ (`Σ` X P)

  `sup`  : ∀ {n} {Γ : Context n} {T : Ty (suc n)} → Tm (Γ -, (`μ` T)) T → Tm Γ (`μ` T)

  -- Easy to use, maybe annoying to do proofs about?
  `v`    : ∀ {n} {Γ : Context n} {x : Fin n} → Tm (unwind Γ x) (lookup Γ x) → Tm Γ (`var` x)
