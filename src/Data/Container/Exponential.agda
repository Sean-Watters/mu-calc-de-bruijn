
module Data.Container.Exponential where

open import Axiom.Extensionality.Propositional using (Extensionality) renaming (implicit-extensionality to exti)
open import Level
open import Data.Container hiding (refl)
open import Data.Container.Combinator using () renaming (_×_ to _⟨×⟩_)
open import Data.Container.Relation.Unary.Any as ◇ using (any)
open import Data.Maybe
open import Data.Product as Product hiding (curry; uncurry)
open import Data.Sum as Sum
open import Function
open import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary.Isomorphism

private variable
  ℓ : Level

-- The exponential container. AKA the internal hom of containers.
-- Due to (Altenkirch, Levy, and Staton; 2010)
_⟨⇒⟩_ : (C D : Container ℓ ℓ) → Container ℓ ℓ
(C ⟨⇒⟩ D) .Shape = (s : C .Shape) → ⟦ D ⟧ (Maybe (C .Position s))
(C ⟨⇒⟩ D) .Position fw = Σ[ s ∈ C .Shape ] (◇ D (_≡ nothing) (fw s))


----------------------------------
-- Currying.

-- The forwards pass.
curry-fw : {X Y Z : Container ℓ ℓ}
         → (X ⟨×⟩ Y) ⇒ Z
         → (sx : Shape X) (sy : Shape Y)
         → Σ[ sz ∈ Shape Z ] (Position Z sz → Maybe (Position Y sy))
curry-fw (fw ▷ bw) sx sy = (fw (sx , sy)) , (isInj₂ ∘ bw)

-- The backwards pass.
curry-bw : {X Y Z : Container ℓ ℓ}
         → (f : (X ⟨×⟩ Y) ⇒ Z)
         → {sx : Shape X}
         → Σ[ sy ∈ Shape Y ] (◇ Z (_≡ nothing) (curry-fw f sx sy))
         → Position X sx
curry-bw (fw ▷ bw) (sy , p)
  = let (zp , f) = ◇.proof p
        x+y = bw zp
    in lemma x+y f where

    lemma : ∀ {X Y : Set ℓ} (p : X ⊎ Y)
          → isInj₂ p ≡ nothing
          → X
    lemma (inj₁ x) refl = x


curry : ∀ {X Y Z : Container ℓ ℓ}
      → (X ⟨×⟩ Y) ⇒ Z
      → X ⇒ (Y ⟨⇒⟩ Z)
curry f .shape = curry-fw f
curry f .position = curry-bw f


----------------------------------
-- Uncurrying.

-- The forwards pass.
uncurry-fw : ∀ {X Y Z : Container ℓ ℓ}
           → X ⇒ (Y ⟨⇒⟩ Z)
           → Shape X × Shape Y
           → Shape Z
uncurry-fw (fw ▷ bw) (sx , sy) = fw sx sy .proj₁

-- The backwards pass.
uncurry-bw : ∀ {X Y Z : Container ℓ ℓ}
           → (f : X ⇒ (Y ⟨⇒⟩ Z))
           → {sxy : Shape X × Shape Y}
           → Position Z (uncurry-fw f sxy)
           → Position X (sxy .proj₁) ⊎ Position Y (sxy .proj₂)
uncurry-bw {X = X} {Y = Y} {Z = Z} (fw ▷ bw) {sx , sy} pz with fw sx sy .proj₂ pz in eq
... | (just y) = inj₂ y
... | nothing = inj₁ (bw (sy , any (pz , eq)))


uncurry : ∀ {X Y Z : Container ℓ ℓ}
        → X ⇒ (Y ⟨⇒⟩ Z)
        → (X ⟨×⟩ Y) ⇒ Z
uncurry f .shape = uncurry-fw f
uncurry f .position = uncurry-bw f


----------------------------------

-- `_⟨×⟩ Y` is left adjoint to `Y ⟨⇒⟩_`,
-- with the data of the natural isomorphism of hom sets being given by
-- `curry` and `uncurry`
module Correct (funext : Extensionality ℓ ℓ) where

  -- Eta for container morphisms with definitionally equal forwards passes
  η' : {X Y : Container ℓ ℓ}
     → (fw : Shape X → Shape Y)
     → { fp gp : {s : Shape X} → Position Y (fw s) → Position X s }
     → (λ {s} → fp {s = s}) ≡ gp
     → _≡_ {A = X ⇒ Y} (fw ▷ fp) (fw ▷ gp)
  η' fw refl = refl

  funext-inv : ∀ {x y} {X : Set x} {Y : Set y} {f g : X → Y}
             → f ≡ g
             → ∀ x → f x ≡ g x
  funext-inv refl _ = refl

  -- Extensional version
  η : {X Y : Container ℓ ℓ}
    → {fs gs : Shape X → Shape Y}
    → {fp : {s : Shape X} → Position Y (fs s) → Position X s }
    → {gp : {s : Shape X} → Position Y (gs s) → Position X s }
    → (eq : fs ≡ gs)
    → ({x : Shape X} → (y : Position Y (fs x)) → fp y ≡ gp (subst (Position Y) (funext-inv eq x) y))
    → _≡_ {A = X ⇒ Y} (fs ▷ fp) (gs ▷ gp)
  η {X = X} {Y} {fs} {gs} {fp} {gp} refl eq2 = η' fs (exti funext (λ {x} → funext λ y → eq2 y))

  -- curry/uncurry are mutual inverses

  uc-c-fw : {X Y Z : Container ℓ ℓ}
          → (f : (X ⟨×⟩ Y) ⇒ Z)
          → f .shape ≡ uncurry-fw (curry-fw f ▷ curry-bw f)
  uc-c-fw (fw ▷ bw) = funext (λ {(sx , sy) → refl})

  uc-c-bw : {X Y Z : Container ℓ ℓ} (f : (X ⟨×⟩ Y) ⇒ Z)
          → (eq : f .shape ≡ uncurry-fw (curry-fw f ▷ curry-bw f))
          → {x : Shape (X ⟨×⟩ Y)} (y : Position Z (f .shape x))
          → f .position y ≡ uncurry (curry f) .position (subst (Position Z) (funext-inv eq x) y)
  uc-c-bw {X} {Y} {Z} (fw ▷ bw) refl {x} y = {!!} -- cursed stuck `with`. Probably need to change the type in some way

  uncurry-curry : {X Y Z : Container ℓ ℓ}
                → (f : (X ⟨×⟩ Y) ⇒ Z)
                → f ≡ uncurry (curry f)
  uncurry-curry f = η (uc-c-fw f) (uc-c-bw f _)



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
