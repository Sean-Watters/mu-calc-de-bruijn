
module ContainerSyntax.Morphism where

open import ContainerSyntax.Base
open import ContainerSyntax.Semantics

-- To define a polymorphic function, we have to pattern match,
-- which means saying what to do for all the constructors.
record _⇒_ (X Y : `Set`) : Set₁ where
  field
    `1-tt` : ⟦ Y ⟧ε

    `+-inj₁` : {X-sum : Sum X}
             → ⟦ SumL X-sum ⟧ε → ⟦ Y ⟧ε
    `+-inj₂` : {X-sum : Sum X}
             → ⟦ SumR X-sum ⟧ε → ⟦ Y ⟧ε

    _`×-,`_ : {X-pair : Product X}
            → ⟦ ProdL X-pair ⟧ε → ⟦ ProdR X-pair ⟧ε → ⟦ Y ⟧ε

    _`Σ-,`_ : {X-sigma : Sigma X}
            → SigmaL X-sigma → ((p : SigmaL X-sigma) → ⟦ SigmaR X-sigma p ⟧ε) → `Set`

    `μ-sup`_ : {X-mu : Mu X}
             → ⟦ MuSup X-mu ⟧ ([] -, X) → `Set`
