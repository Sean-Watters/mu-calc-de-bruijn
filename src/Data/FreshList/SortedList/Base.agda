open import Relation.Binary
open import Data.FreshList.InductiveInductive
open import Data.List using (List; []; _∷_)
open import Data.Nat renaming (_<_ to _<ℕ_)
open import Data.Nat.Properties renaming (<-trans to <ℕ-trans)
open import Data.Nat.Induction
open import Data.Sum
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Induction.WellFounded

open import Algebra.Structures.OICM

module Data.FreshList.SortedList.Base
  {X : Set} {_≈_ : X → X → Set} {_<_ : X → X → Set}
  (<-STO : IsPropStrictTotalOrder _≈_ _<_)
  where

private
  ≈-Eq = IsPropStrictTotalOrder.isEquivalence <-STO
  ≈-sym = IsEquivalence.sym ≈-Eq
  <-tri = IsPropStrictTotalOrder.compare <-STO
  <-trans = IsPropStrictTotalOrder.trans <-STO
  <-resp-≈ = IsPropStrictTotalOrder.<-resp-≈ <-STO
  _≈?_ = IsPropStrictTotalOrder._≟_ <-STO
  open WithEq _<_ ≈-Eq <-resp-≈

SortedList : Set
SortedList = List# _<_

opaque
  -- The union or merge of two lists is defined using wellfounded
  -- recursion on their total length; sometimes we decrease the length
  -- of the first list, sometimes the second. We also simultaneously
  -- prove that if a is fresh for two lists, then it is also fresh for
  -- their union.
  union : (xs ys : SortedList) → Acc _<ℕ_ (length xs + length ys) → SortedList
  union-fresh : {a : X} {xs ys : SortedList} {p : Acc _<ℕ_ (length xs + length ys)} → a # xs → a # ys → a # (union xs ys p)

  union [] ys rs = ys
  union (cons x xs x#xs) [] rs = cons x xs x#xs
  union (cons x xs x#xs) (cons y ys y#ys) (acc rs) with <-tri x y
  ... | tri< x<y x≉y y≮x = cons x (union xs (cons y ys y#ys) (rs ≤-refl)) (union-fresh x#xs (x<y ∷ (#-trans <-trans x y ys x<y y#ys)))
  ... | tri≈ x≮y x≈y y≮x = cons x (union xs ys (rs (s≤s (≤-trans (n≤1+n _) (≤-reflexive $ sym $ +-suc _ _))))) (union-fresh x#xs (#-resp-≈ y#ys (≈-sym x≈y)))
  ... | tri> x≮y x≉y y<x = cons y (union (cons x xs x#xs) ys (rs (s≤s (≤-reflexive $ sym $ +-suc _ _)))) (union-fresh (y<x ∷ #-trans <-trans y x xs y<x x#xs) y#ys)

  union-fresh {a} {[]} {ys} {acc rs} a#xs a#ys = a#ys
  union-fresh {a} {cons x xs x#xs} {[]} {acc rs} a#xs a#ys = a#xs
  union-fresh {a} {cons x xs x#xs} {cons y ys y#ys} {acc rs} (a<x ∷ a#xs) (a<y ∷ a#ys) with <-tri x y
  ... | tri< x<y x≉y y≮x = a<x ∷ union-fresh a#xs (a<y ∷ a#ys)
  ... | tri≈ x≮y x≈y y≮x = a<x ∷ (union-fresh a#xs a#ys)
  ... | tri> x≮y x≉y y<x = a<y ∷ union-fresh (a<x ∷ a#xs) a#ys

  -- The top-level operation we really want
  _∪_ : SortedList → SortedList → SortedList
  xs ∪ ys = union xs ys (<-wellFounded (length xs + length ys))


insert : X → SortedList → SortedList
insert x xs = cons x [] [] ∪ xs

_∩_ : SortedList -> SortedList -> SortedList
[] ∩ ys = []
_∩_ (cons x xs p) ys with any? (x ≈?_) ys
... | yes _ = insert x (xs ∩ ys)
... | no  _ = xs ∩ ys

insertion-sort : List X → SortedList
insertion-sort [] = []
insertion-sort (x ∷ xs) = insert x (insertion-sort xs)

-- Element removal
mutual
  _-[_] : SortedList → X → SortedList
  [] -[ y ] = []
  cons x xs x#xs -[ y ] with x ≈? y
  ... | yes _ = xs
  ... | no  _ = cons x (xs -[ y ]) (-[]-fresh xs y x x#xs)

  -[]-fresh : (xs : SortedList) → (y : X) → (z : X) → z # xs → z # (xs -[ y ])
  -[]-fresh [] y x z#xs = z#xs
  -[]-fresh (cons x xs x#xs) y z (z≠x ∷ z#xs) with x ≈? y
  ... | yes _ = z#xs
  ... | no  _ = z≠x ∷ -[]-fresh xs y z z#xs

  -- remove-fresh-idempotent : (xs : SortedList) → (y : X) → y # xs → xs -[ y ] ≡ xs
  -- remove-fresh-idempotent [] y y#xs = refl
  -- remove-fresh-idempotent (cons x xs x#xs) y (y≠x ∷ y#xs) with ≠-dec x y
  -- ... | inj₁ x≈y = ⊥-elim (≠-irrefl x≈y (≠-sym y≠x))
  -- ... | inj₂ x≠y = ≠-cons-cong refl (remove-fresh-idempotent xs y y#xs)

  -- remove-removes : (xs : SortedList) → (y : X) → y # (xs -[ y ])
  -- remove-removes [] y = []
  -- remove-removes (cons x xs x#xs) y with ≠-dec x y
  -- ... | inj₁ x≈y = ≠-resp-≈ x≈y x#xs
  -- ... | inj₂ x≠y = ≠-sym x≠y ∷ remove-removes xs y

-- Set difference
_-<_> : SortedList → SortedList → SortedList
xs -< [] > = xs
xs -< cons x ys x#xs > = (xs -[ x ]) -< ys >
