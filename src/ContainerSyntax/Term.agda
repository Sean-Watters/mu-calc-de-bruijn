{-# OPTIONS --guardedness #-}
module ContainerSyntax.Term where

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.String
open import Data.Product
open import Data.Sum
open import Data.Fin

open import ContainerSyntax.Type

mutual
  data Tm {n : ℕ} (Γ : Context n) : Ty n → Set₁ where
    `tt`   : Tm Γ `1`

    `injL` : {L R : Ty n} → Tm Γ L → Tm Γ (L `+` R)
    `injR` : {L R : Ty n} → Tm Γ R → Tm Γ (L `+` R)

    _`,`_  : {L R : Ty n} → Tm Γ L → Tm Γ R → Tm Γ (L `×` R)
    _`,,`_ : {X : Set} {P : X → Ty n} → (x : X) → Tm Γ (P x) → Tm Γ (`Σ` X P)

    `sup`  : {T : Ty (suc n)} → Tm (Γ -, (`μ` T)) T → Tm Γ (`μ` T)
    `inf`  : {T : Ty (suc n)} → ∞Tm (Γ -, (`ν` T)) T → Tm Γ (`ν` T)

    -- Easy to use, maybe annoying to do proofs about?
    `v`    : {x : Fin n} → Tm (unwind Γ x) (lookup Γ x) → Tm Γ (`var` x)

  record ∞Tm {n : ℕ} (Γ : Context n) (ty : Ty n) : Set₁ where
    constructor ♯
    coinductive
    field
      ♭ : Tm Γ ty

-- Finite terms.
data Finite {n : ℕ} {Γ : Context n} : {ty : Ty n} → Tm Γ ty → Set₁ where
    `tt`   : Finite `tt`

    `injL` : {L R : Ty n} {l : Tm Γ L} → Finite l → Finite {ty = L `+` R} (`injL` l)
    `injR` : {L R : Ty n} {r : Tm Γ L} → Finite r → Finite {ty = L `+` R}(`injL` r)

    _`,`_  : {L R : Ty n} {l : Tm Γ L} {r : Tm Γ R} → Finite l → Finite r → Finite (l `,` r)
    _`,,`_ : {X : Set} {P : X → Ty n} → (x : X) → { px : Tm Γ (P x)} → Finite px → Finite {ty = `Σ` X P} (x `,,` px)

    `sup`  : {T : Ty (suc n)} (x : Tm (Γ -, (`μ` T)) T) → Finite x → Finite (`sup` x)
    `inf`  : {T : Ty (suc n)} (x : Tm (Γ -, (`ν` T)) T) → Finite x → Finite (`inf` (♯ x))

    `v`    : {x : Fin n} {Γ!!x : Tm (unwind Γ x) (lookup Γ x)} → Finite Γ!!x → Finite (`v` Γ!!x)
