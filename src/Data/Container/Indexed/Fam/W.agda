{-# OPTIONS --safe #-}
module Data.Container.Indexed.Fam.W where

open import Level
open import Axiom.Extensionality.Propositional using (Extensionality) renaming (implicit-extensionality to exti)
open import Data.Product using (_,_; -,_; proj₁; proj₂)
open import Function

open import Relation.Binary.PropositionalEquality hiding (J)

open import Data.Container.Indexed.Fam.Base
open import Data.Container.Indexed.Fam.Morphism
open import Data.Container.Indexed.Fam.Relation.Unary.All
open Container

private variable
  I J : Set

-- Indexed W-types. AKA how to generate families of inductive data types
-- from indexed containers.
-- W-types are trees with node arity given by the set of shapes, and
data W {J : Set} (C : Container J J) : J → Set where
  sup : ∀ {j} → ⟦ C ⟧ (W C) j → W C j


head : {C : Container J J}
    → ∀ {j} → W C j → Shape C j
head (sup (s , f)) = s

tail : {C : Container J J}
    → ∀ {j} → (x : W C j) → Position C (head x) j → W C j
tail (sup (s , f)) = f

map : ∀ {C D : Container J J}
    → C ⇒ D
    → (∀ {j} → W C j → W D j)
map m (sup (s , f)) = sup (⟪ m ⟫ (s , λ p → map m (f p)))


module _ {C : Container J J}
         (P : ∀ {j} → W C j → Set)
         (algebra : ∀ {j} → {t : ⟦ C ⟧ (W C) j} → □ C P t → P (sup t)) where

  induction : ∀ {j} → (w : W C j) → P w
  induction (sup (s , f)) = algebra (all ((induction ∘ f) _))

module _ (ext : Extensionality 0ℓ 0ℓ)
         {C : Container J J}
         (P : ∀ {j} → W C j → Set)
         (algebra : ∀ {j} (t : ⟦ C ⟧ (W C) j) → □ C P t → P (sup t)) where

  -- induction-unique : (β : (j : J) → (w : W C j) → P w)
  --                  → (∀ (j : J) (s : ⟦ C ⟧ (W C) j) → {!!} ≡ algebra ((s .proj₁ , {!β _!} ∘ (s .proj₂))) {!!})
  --                  → (∀ (j : J) → {!!})
  -- induction-unique = {!!}

-- fold, the unique algebra morphism that sends any arbitrary algebra to the initial algebra
module _ {C : Container J J}
         (P : J → Set)
         (algebra : ∀ {j} → ⟦ C ⟧ P j → P j) where

  fold : ∀ {j} → W C j → P j
  fold = induction (λ {j} _ → P j) (λ x → algebra (-, λ p → □.proof x {p = p}))

module _ (ext : Extensionality 0ℓ 0ℓ)
         {C : Container J J}
         (P : J → Set)
         (algebra : ∀ {j} → ⟦ C ⟧ P j → P j) where

  fold-unique : (β : ∀ (j : J) → W C j → P j)
              → (∀ (j : J) (s : ⟦ C ⟧ (W C) j) → β j (sup s) ≡ algebra (s .proj₁ , (β _) ∘ (s .proj₂)))
              → (∀ (j : J) (x : W C j) → β j x ≡ fold P algebra x)
  fold-unique β commβ j (sup (s , g)) =
    begin
      β j (sup (s , g))
    ≡⟨ commβ j (s , g) ⟩
      algebra {j} (s , β _ ∘ g)
    ≡⟨ cong (algebra {j}) (cong (s ,_) (exti ext (ext (λ p → fold-unique β commβ _ (g p))))) ⟩
      algebra {j} (s , λ p →
                          induction (λ {j = j₁} _ → P j₁)
                          (λ x → algebra (-, (λ p₁ → □.proof x))) (g p))
    ≡⟨⟩
      fold P algebra (sup (s , g))
    ∎ where open ≡-Reasoning
