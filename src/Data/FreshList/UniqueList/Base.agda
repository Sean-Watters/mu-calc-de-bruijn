open import Algebra.Structures.OICM

module Data.FreshList.UniqueList.Base
  {X : Set} {_≈_ : X → X → Set} {_≠_ : X → X → Set}
  (≠-AR : IsPropDecTightApartnessRelation _≈_ _≠_)
  where

open import Data.FreshList.InductiveInductive
open import Data.Sum

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Nullary using (Dec; yes; no)
open import Data.Product
open import Data.Empty


private
  ≠-irrefl  = IsPropDecTightApartnessRelation.irrefl ≠-AR
  ≠-sym  = IsPropDecTightApartnessRelation.sym ≠-AR
  ≠-cotrans = IsPropDecTightApartnessRelation.cotrans ≠-AR
  ≠-prop = IsPropDecTightApartnessRelation.prop ≠-AR
  ≠-dec = IsPropDecTightApartnessRelation.eqOrApart ≠-AR

  ≠-cons-cong = WithIrr.cons-cong _≠_ ≠-prop

_≟_ : Decidable _≈_
x ≟ y with ≠-dec x y
... | inj₁ x≈y = yes x≈y
... | inj₂ x≠y = no λ x≈y → ≠-irrefl x≈y x≠y

UniqueList : Set
UniqueList = List# _≠_

≠-resp-≈ : ∀ {x y xs} → x ≈ y → _#_ {R = _≠_} x xs → y # xs
≠-resp-≈ x≈y [] = []
≠-resp-≈ {x} {y} {xs} x≈y (z≠x ∷ x#xs) with ≠-cotrans z≠x y
... | inj₁ x≠y = ⊥-elim (≠-irrefl x≈y x≠y)
... | inj₂ y≠z = y≠z ∷ ≠-resp-≈ x≈y x#xs

---------------------
-- Element Removal --
---------------------

mutual
  _-[_] : UniqueList → X → UniqueList
  [] -[ y ] = []
  cons x xs x#xs -[ y ] with ≠-dec x y
  ... | inj₁ x≈y = xs
  ... | inj₂ x≠y = cons x (xs -[ y ]) (-[]-fresh xs y x x#xs)

  -[]-fresh : (xs : UniqueList) → (y : X) → (z : X) → z # xs → z # (xs -[ y ])
  -[]-fresh [] y x z#xs = z#xs
  -[]-fresh (cons x xs x#xs) y z (z≠x ∷ z#xs) with ≠-dec x y
  ... | inj₁ x≈y = z#xs
  ... | inj₂ x≠y = z≠x ∷ -[]-fresh xs y z z#xs

  remove-fresh-idempotent : (xs : UniqueList) → (y : X) → y # xs → xs -[ y ] ≡ xs
  remove-fresh-idempotent [] y y#xs = refl
  remove-fresh-idempotent (cons x xs x#xs) y (y≠x ∷ y#xs) with ≠-dec x y
  ... | inj₁ x≈y = ⊥-elim (≠-irrefl x≈y (≠-sym y≠x))
  ... | inj₂ x≠y = ≠-cons-cong refl (remove-fresh-idempotent xs y y#xs)

  remove-removes : (xs : UniqueList) → (y : X) → y # (xs -[ y ])
  remove-removes [] y = []
  remove-removes (cons x xs x#xs) y with ≠-dec x y
  ... | inj₁ x≈y = ≠-resp-≈ x≈y x#xs
  ... | inj₂ x≠y = ≠-sym x≠y ∷ remove-removes xs y

----------------
-- Merge Sort --
----------------

-- We remove later elements in the list, if they occur
union : UniqueList → UniqueList  → UniqueList
union [] ys = ys
union (cons x xs x#xs) ys = cons x (union xs ys -[ x ]) (remove-removes (union xs ys) x)

union-fresh : {a : X} {xs ys : UniqueList} → a # xs → a # ys → a # (union xs ys)
union-fresh {xs = []} a#xs a#ys = a#ys
union-fresh {xs = cons x xs x#xs} (a≠x ∷ a#xs) a#ys = a≠x ∷ -[]-fresh (union xs _) x _ (union-fresh a#xs a#ys)

insert : X → UniqueList → UniqueList
insert x xs = union (cons x [] []) xs
