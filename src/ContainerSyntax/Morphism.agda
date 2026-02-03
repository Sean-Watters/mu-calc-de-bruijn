
module ContainerSyntax.Morphism where

open import ContainerSyntax.Base
open import ContainerSyntax.Semantics renaming (⟦_⟧ to ⟦_⟧ty)

open import Data.Empty
open import Data.Unit
open import Data.Sum renaming ([_,_] to join)
open import Data.Product
open import Data.Vec
open import Data.Fin hiding (join)
open import Data.Nat

open import Function

open import Data.Container.Indexed.Fam
open import Data.Container.Indexed.Fam.Morphism as Lens hiding (_⇒_)

-- To define a polymorphic function, we have to pattern match,
-- which means saying what to do for all the constructors.
-- We apply the identity at variables.
record _⇒_ {n : ℕ} (X Y : Ty n) : Set₁ where
  field
    `1-tt` : ∀ Γ → ⟦ Y ⟧ty Γ

    `+-inj₁` : {X-sum : Sum X}
             → ∀ Γ → ⟦ SumL X-sum ⟧ty Γ → ⟦ Y ⟧ty Γ
    `+-inj₂` : {X-sum : Sum X}
             → ∀ Γ → ⟦ SumR X-sum ⟧ty Γ → ⟦ Y ⟧ty Γ

    _`×-,`_ : {X-pair : Product X}
            → ∀ Γ → ⟦ ProdL X-pair ⟧ty Γ → ⟦ ProdR X-pair ⟧ty Γ → ⟦ Y ⟧ty Γ

    _`Σ-,`_ : {X-sigma : Sigma X}
            → ∀ Γ → SigmaL X-sigma → ((p : SigmaL X-sigma) → ⟦ SigmaR X-sigma p ⟧ty Γ) → ⟦ Y ⟧ty Γ

    `μ-sup`_ : {X-mu : Mu X}
             → ∀ Γ → ⟦ MuSup X-mu ⟧ty (Γ -, X) → ⟦ Y ⟧ty Γ
open _⇒_

-- TODO - implement lens semantics
AsLens : {X Y : `Set`} → X ⇒ Y → (AsCont X) Lens.⇒ (AsCont Y)
AsLens {`0`} {Y} f = ⟨⊥-elim⟩
AsLens {`1`} {Y} f = (const (`1-tt` f [] .proj₁)) ▷ λ { {i = ()} }
AsLens {Xl `+` Xr} {Y} f = join {!`+-inj₁` f []!} {!!} ▷ {!!}

AsLens {Xl `×` Xr} {Y} f = {!!}
AsLens {`Σ` Xl Xr} {Y} f = {!!}
AsLens {`μ` X} {Y} f = {!!}

-- TODO - extension of that lens to a polymorphic function

-- TODO - directly implement function semantics

-- TODO - correctness proof - they coincide
