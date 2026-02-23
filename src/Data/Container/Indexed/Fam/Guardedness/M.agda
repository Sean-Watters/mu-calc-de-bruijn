{-# OPTIONS --guardedness #-}

-- From Indexed Containers, Altenkirch et al 2015
module Data.Container.Indexed.Fam.Guardedness.M where

open import Level
open import Axiom.Extensionality.Propositional
open import Codata.Musical.Notation
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

open import Data.Container.Indexed.Fam.Base

private variable
  I : Set

data M {I : Set} (C : Container I I) : I → Set where
  inf : ∀ {i} → ⟦ C ⟧ (λ i → ∞ (M C i)) i → M C i

-- Thanks to the ∞ in `inf`, we can invert it to get something that
-- looks more like a coalgebra.
inf-inverse : ∀ {I} {C : Container I I}
            → ∀ {i} → M C i → ⟦ C ⟧ (M C) i
inf-inverse (inf (s , f)) .proj₁ = s
inf-inverse (inf (s , f)) .proj₂ p = ♭ (f p)


-- Bisimulations of M types
data _≈_ {I : Set} {C : Container I I} {i : I} : (x y : M C i) → Set where
  inf : {s s' : C .Shape i}
      → {f : ∀ {i'} → C .Position s  i' → ∞ (M C i')}
      → {g : ∀ {i'} → C .Position s' i' → ∞ (M C i')}
      → (eq : s ≡ s')
      → (∀ {i'} (p : C .Position s i') → ∞ (♭ (f p) ≈ ♭ (g (subst (λ s → C .Position s i') eq p))))
      → inf (s , f) ≈ inf (s' , g)

≈trans : {C : Container I I} {i : I} {x y z : M C i}
       → x ≈ y → y ≈ z → x ≈ z
≈trans (inf refl u) (inf refl v) = inf refl (λ p → ♯ (≈trans (♭ (u p)) (♭ (v p))))

-- Lifing bisim on `M C` to bisim on `⟦ C ⟧ (M C)`
_≈⟦-⟧M≈_ : {C : Container I I} {i : I}
         → (x y : ⟦ C ⟧ (M C) i) → Set
_≈⟦-⟧M≈_ {I} {C} (s , f) (s' , f') = Σ[ eq ∈ (s ≡ s') ] (∀ {i'} (p : C .Position s i') → f p ≈ f' (subst (λ s → C .Position s i') eq p))

-- unfold, the unique coalgebra morphism that sends any arbitrary coalgebra to the terminal coalgebra
module _ {C : Container I I}
         (P : I → Set)
         (coalgebra : ∀ {i} → P i → ⟦ C ⟧ P i) where

  unfold : ∀ {i} → P i → M C i
  unfold x with coalgebra x
  ... | s , f = inf (s , λ p → ♯ unfold (f p))

module _ (ext : Extensionality 0ℓ 0ℓ)
         {C : Container I I}
         (P : I → Set)
         (coalgebra : ∀ {i} → P i → ⟦ C ⟧ P i) where

  {-# TERMINATING #-} -- only needed because I cba inlining ≈trans. TODO: do that.
  unfold-unique : (β : {i : I} → P i → M C i)
                → (∀ {i : I} (p : P i) → inf-inverse (β p) ≈⟦-⟧M≈ ⟦ C ⟧-map β (coalgebra p) )
                → (∀ {i : I} (p : P i) → β p ≈ unfold P coalgebra p)
  unfold-unique β commβ p with β p | commβ p
  unfold-unique β commβ p | inf (_ , f) | refl , bs = inf refl λ q → ♯ (≈trans (bs q) (unfold-unique β commβ (coalgebra p .proj₂ q) ))
