
module Data.Container.Exponential where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Level
open import Data.Container hiding (refl)
open import Data.Container.Combinator using () renaming (_×_ to _⟨×⟩_)
open import Data.Container.Relation.Unary.Any as ◇ using (any)
open import Data.Maybe
open import Data.Product as Product hiding (curry; uncurry)
open import Data.Sum as Sum
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Isomorphism

private variable
  ℓ : Level

-- The exponential container. AKA the internal hom of containers.
-- Due to (Altenkirch, Levy, and Staton; 2010)
_⟨⇒⟩_ : (C D : Container ℓ ℓ) → Container ℓ ℓ
(C ⟨⇒⟩ D) .Shape = (s : C .Shape) → ⟦ D ⟧ (Maybe (C .Position s))
(C ⟨⇒⟩ D) .Position fw = Σ[ s ∈ C .Shape ] (◇ D (_≡ nothing) (fw s))


curry : ∀ {X Y Z : Container ℓ ℓ}
      → (X ⟨×⟩ Y) ⇒ Z
      → X ⇒ (Y ⟨⇒⟩ Z)
curry (fw ▷ bw) .shape sx sy = (fw (sx , sy)) , (isInj₂ ∘ bw)
curry (fw ▷ bw) .position (sy , p)
  = let (zp , f) = ◇.proof p
        x+y = bw zp
    in lemma x+y f where

    lemma : ∀ {X Y : Set ℓ} (p : X ⊎ Y)
          → isInj₂ p ≡ nothing
          → X
    lemma (inj₁ x) refl = x


uncurry : ∀ {X Y Z : Container ℓ ℓ}
        → X ⇒ (Y ⟨⇒⟩ Z)
        → (X ⟨×⟩ Y) ⇒ Z
uncurry (fw ▷ bw) .shape (sx , sy) = fw sx sy .proj₁
uncurry {X = X} {Y} {Z} (fw ▷ bw) .position {sx , sy} pz = x+y where
  1+y : Maybe (Position Y sy)
  1+y = fw sx sy .proj₂ pz

  x+y : Position X sx ⊎ Position Y sy
  x+y with 1+y in eq
  ... | (just y) = inj₂ y
  ... | nothing = inj₁ (bw (sy , any (pz , eq)))


module Correct (funext : Extensionality ℓ ℓ) where

  -- curry/uncurry are mutual inverses

  uncurry-curry : {X Y Z : Container ℓ ℓ}
                → (f : (X ⟨×⟩ Y) ⇒ Z)
                → f ≡ uncurry (curry f)
  uncurry-curry (fw ▷ bw) = {!!}

  curry-uncurry : {X Y Z : Container ℓ ℓ}
                → (f : X ⇒ (Y ⟨⇒⟩ Z))
                → f ≡ curry (uncurry f)
  curry-uncurry (fw ▷ bw) = {!!}


  -- and they are natural in all 3 variables

  natural₁ : {!!}
  natural₁ = {!!}

  natural₂ : {!!}
  natural₂ = {!!}

  natural₃ : {!!}
  natural₃ = {!!}
