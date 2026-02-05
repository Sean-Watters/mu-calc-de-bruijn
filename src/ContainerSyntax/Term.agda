
module ContainerSyntax.Term where

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.String
open import Data.Product
open import Data.Sum
open import Data.Fin

open import ContainerSyntax.Base

data Tm : {n : ℕ} → Ty n → Set₁ where
  `tt` : ∀ {n} → Tm {n} `1`

  `injL` : ∀ {n} {L R : Ty n} → Tm L → Tm (L `+` R)
  `injR` : ∀ {n} {L R : Ty n} → Tm R → Tm (L `+` R)

  _`,`_  : ∀ {n} {L R : Ty n} → Tm L → Tm R → Tm (L `×` R)

  _`,,`_ : ∀ {n} {X : Set} {P : X → Ty n} → (x : X) → Tm (P x) → Tm (`Σ` X P)

  `sup` : ∀ {n} {T : Ty (suc n)} → Tm T → Tm (`μ` T)

  `v` : ∀ {n : ℕ} {x : Fin n} → Tm (`var` (suc x)) -- TODO - placeholder? what data do we need? lookup in context?
