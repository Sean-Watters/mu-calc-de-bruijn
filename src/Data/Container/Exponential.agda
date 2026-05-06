
module Data.Container.Exponential where

open import Axiom.Extensionality.Propositional using (Extensionality) renaming (implicit-extensionality to exti)
open import Level
open import Data.Container hiding (refl)
open import Data.Container.Combinator using () renaming (_×_ to _⟨×⟩_)
open import Data.Container.Relation.Unary.Any as ◇ using (any)
open import Data.Maybe
open import Data.Product as Product hiding (curry; uncurry)
open import Data.Product.Properties using ( Σ-≡,≡→≡)
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
         → (sx : Shape X)
         → (sy : Shape Y) → Σ[ sz ∈ Shape Z ] (Position Z sz → Maybe (Position Y sy))
curry-fw (fw ▷ bw) sx sy = (fw (sx , sy)) , (isInj₂ ∘ bw)

isInj₂-lemma : ∀ {X Y : Set ℓ} (p : X ⊎ Y)
             → isInj₂ p ≡ nothing
             → X
isInj₂-lemma (inj₁ x) refl = x

-- The backwards pass.
curry-bw : {X Y Z : Container ℓ ℓ}
         → (f : (X ⟨×⟩ Y) ⇒ Z)
         → {sx : Shape X}
         → Σ[ sy ∈ Shape Y ] (◇ Z (_≡ nothing) (curry-fw f sx sy))
         → Position X sx
curry-bw (fw ▷ bw) (sy , p)
  = let (pz , f) = ◇.proof p
        x+y = bw pz
    in isInj₂-lemma x+y f



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
uncurry-bw' : ∀ {X Y Z : Container ℓ ℓ}
            → (f : X ⇒ (Y ⟨⇒⟩ Z))
            → {sxy : Shape X × Shape Y}
            → (pz : Position Z (uncurry-fw f sxy))
            -- Manually unrolling the `with` because later proofs get stuck hard on it otherwise.
            → (m : Maybe (Position Y (sxy .proj₂))) (m-eq : f .shape (sxy .proj₁) (sxy .proj₂) .proj₂ pz ≡ m)
            → Position X (sxy .proj₁) ⊎ Position Y (sxy .proj₂)
uncurry-bw' (fw ▷ bw) {sx , sy} pz (just y) m-eq = inj₂ y
uncurry-bw' (fw ▷ bw) {sx , sy} pz nothing m-eq = inj₁ (bw (sy , any (pz , m-eq)))


uncurry-bw : ∀ {X Y Z : Container ℓ ℓ}
           → (f : X ⇒ (Y ⟨⇒⟩ Z))
           → {sxy : Shape X × Shape Y}
           → Position Z (uncurry-fw f sxy)
           → Position X (sxy .proj₁) ⊎ Position Y (sxy .proj₂)
uncurry-bw f pz = uncurry-bw' f pz _ refl


uncurry : ∀ {X Y Z : Container ℓ ℓ}
        → X ⇒ (Y ⟨⇒⟩ Z)
        → (X ⟨×⟩ Y) ⇒ Z
uncurry f .shape = uncurry-fw f
uncurry f .position = uncurry-bw f


----------------------------------

-- `_⟨×⟩ Y` is left adjoint to `Y ⟨⇒⟩_`,
-- with the data of the natural isomorphism of hom sets being given by
-- `curry` and `uncurry`.
-- Warning: the details get very technical due to boring reasons (something something dependent types).
-- The actual conceptual content is basically zero; these are trivial, just not trivially so.
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

  uc-c-bw' : {X Y Z : Container ℓ ℓ} (f : (X ⟨×⟩ Y) ⇒ Z)
           → {sxy : Shape (X ⟨×⟩ Y)} (z : Position Z (f .shape sxy))
           -- Another very specific hand-rolled with-abstraction. This feels like dark magic at this point.
           → (m : Maybe (Position Y (sxy .proj₂))) (m-eq : curry f .shape (sxy .proj₁) (sxy .proj₂) .proj₂ z ≡ m)
           → f .position z ≡ uncurry-bw' (curry f) z m m-eq
  uc-c-bw' (fw ▷ bw) z (just y) m-eq = lemma m-eq where
    lemma : ∀ {X Y} {w : X ⊎ Y} {y : Y}
          → isInj₂ w ≡ just y
          → w ≡ inj₂ y
    lemma {w = inj₂ y} refl = refl
  uc-c-bw' (fw ▷ bw) z nothing m-eq with bw z
  uc-c-bw' (fw ▷ bw) z nothing refl | inj₁ x = refl

  uc-c-bw : {X Y Z : Container ℓ ℓ} (f : (X ⟨×⟩ Y) ⇒ Z)
          → (eq : f .shape ≡ uncurry-fw (curry-fw f ▷ curry-bw f))
          → {sxy : Shape (X ⟨×⟩ Y)} (z : Position Z (f .shape sxy))
          → f .position z ≡ uncurry (curry f) .position (subst (Position Z) (funext-inv eq sxy) z)
  uc-c-bw f refl z = uc-c-bw' f z _ refl


  -- Dependently typed tarpit out of the way, we have the first side of the iso:

  uncurry-curry : {X Y Z : Container ℓ ℓ}
                → (f : (X ⟨×⟩ Y) ⇒ Z)
                → f ≡ uncurry (curry f)
  uncurry-curry f = η (uc-c-fw f) (uc-c-bw f (uc-c-fw f))


  -- And now for the other direction.

  c-uc-fw : {X Y Z : Container ℓ ℓ}
          → (f : X ⇒ (Y ⟨⇒⟩ Z))
          → f .shape ≡ curry-fw (uncurry-fw f ▷ uncurry-bw f)
  c-uc-fw {X = X} {Y} {Z} (fw ▷ bw) = funext (λ x → funext (λ y → Σ-≡,≡→≡ (refl , (funext (λ z → lemma x y z _ refl))))) where
    lemma : (sx : Shape X) (sy : Shape Y)
          → (pz : Z .Position (fw sx sy .proj₁))
          → (m : Maybe (Position Y sy)) (m-eq : fw sx sy .proj₂ pz ≡ m)
          → m ≡ isInj₂ (uncurry-bw' (fw ▷ bw) pz m m-eq)
    lemma sx sy pz (just py) m-eq = refl
    lemma sx sy pz nothing m-eq = refl

  c-uc-bw : {X Y Z : Container ℓ ℓ}
          → (f : X ⇒ (Y ⟨⇒⟩ Z))
          → {sx : Shape X}
          → (py : Position (Y ⟨⇒⟩ Z) (f .shape sx)) -- which is `Σ[ sy ∈ Y .Shape ] (◇ Z (_≡ nothing) (fw sx sy))`
          → f .position py
          ≡ curry-bw (uncurry f) (subst (λ fw → Σ[ sy ∈ Y .Shape ] (◇ Z (_≡ nothing) (fw sy))) (funext-inv (c-uc-fw f) sx) py)
  c-uc-bw (fw ▷ bw) py = {!!}

  curry-uncurry : {X Y Z : Container ℓ ℓ}
                → (f : X ⇒ (Y ⟨⇒⟩ Z))
                → f ≡ curry (uncurry f)
  curry-uncurry f = η (c-uc-fw f) {! c-uc-bw f (c-uc-fw f) !}


  -- and they are natural in all 3 variables

  natural₁ : {!!}
  natural₁ = {!!}

  natural₂ : {!!}
  natural₂ = {!!}

  natural₃ : {!!}
  natural₃ = {!!}
