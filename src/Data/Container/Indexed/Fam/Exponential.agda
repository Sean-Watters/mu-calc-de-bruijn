
module Data.Container.Indexed.Fam.Exponential where

open import Data.Container.Indexed.Fam.Base
open import Data.Container.Indexed.Fam.Modality
open import Data.Container.Indexed.Fam.Combinator
open import Data.Container.Indexed.Fam.Morphism
open _⇒_
open import Data.Maybe
open import Data.Product hiding (curry; uncurry)
open import Data.Sum
open import Data.Sum.MoreProps
open import Function
open import Relation.Binary.PropositionalEquality hiding (J)

private variable
  I J : Set

_⟨⇒⟩_ : (C D : Container I J) → Container I J
(C ⟨⇒⟩ D) .Shape j = (s : C .Shape j) → ⟦ D ⟧ (λ i → Maybe (C .Position s i)) j
(C ⟨⇒⟩ D) .Position {j} fw i = Σ[ s ∈ C .Shape j ] (◇ D (_≡ nothing) (fw s))

-- Currying

curry-fw : {X Y Z : Container I J}
         → (X ⟨×⟩ Y) ⇒ Z
         → {j : J} → (sx : Shape X j) → Shape (Y ⟨⇒⟩ Z) j
curry-fw (fw ▷ bw) sx sy = (fw (sx , sy)) , isInj₂ ∘ bw

-- The backwards pass.
curry-bw : {X Y Z : Container I J}
         → (f : (X ⟨×⟩ Y) ⇒ Z)
         → {j : J}
         → {sx : Shape X j}
         → {i : I}
         → Position (Y ⟨⇒⟩ Z) (curry-fw f sx) i
         → Position X sx i
curry-bw (fw ▷ bw) {i = i} (sy , p)
  = let (pz , f) = ◇.proof p i
        x+y = bw pz
    in isInj₂-lemma x+y f

curry : ∀ {X Y Z : Container I J}
      → (X ⟨×⟩ Y) ⇒ Z
      → X ⇒ (Y ⟨⇒⟩ Z)
curry f .fw = curry-fw f
curry f .bw = curry-bw f

-- Uncurrying

uncurry-fw : ∀ {X Y Z : Container I J}
           → X ⇒ (Y ⟨⇒⟩ Z)
           → {j : J}
           → Shape X j × Shape Y j
           → Shape Z j
uncurry-fw (fw ▷ bw) (sx , sy) = fw sx sy .proj₁

uncurry-bw : ∀ {X Y Z : Container I J}
           → (f : X ⇒ (Y ⟨⇒⟩ Z))
           → {j : J}
           → {sxy : Shape X j × Shape Y j}
           → {i : I}
           → (pz : Position Z (uncurry-fw f sxy) i)

           -- with f .fw (sxy .proj₁) (sxy .proj₂) .proj₂ pz
           -- But manually unrolled, because pain.
           → (m : Maybe (Position Y (sxy .proj₂) i))
           → (m-eq : f .fw (sxy .proj₁) (sxy .proj₂) .proj₂ pz ≡ m)

           → Position (X ⟨×⟩ Y) sxy i
uncurry-bw (fw ▷ bw) {j} {sx , sy} {i} pz (just y) m-eq
  = inj₂ y
uncurry-bw (fw ▷ bw) {j} {sx , sy} {i} pz nothing m-eq
  = inj₁ (bw (sy , any λ i' → {!pz!} , {!!}))

uncurry : ∀ {X Y Z : Container I J}
        → X ⇒ (Y ⟨⇒⟩ Z)
        → (X ⟨×⟩ Y) ⇒ Z
uncurry f .fw = uncurry-fw f
uncurry f .bw = {!!}
