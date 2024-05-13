{-# OPTIONS --with-K #-}
module Relation.Unary.Finiteness.WithK where

open import Algebra.Structures.Propositional
open import Data.Unit
open import Data.Empty
open import Data.List
open import Data.List.Relation.Unary.Any hiding (lookup)
open import Data.Product
open import Data.List.Membership.Propositional
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.MoreProps renaming (>-isPropStrictTotalOrder to ℕ-STO)
open import Data.Nat.Induction
open import Data.Fin using (Fin; fromℕ; toℕ; inject₁; fromℕ<) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ-inject₁; toℕ-cancel-<; toℕ-fromℕ<)
open import Data.Fin.MoreProps renaming (>-isPropStrictTotalOrder to Fin-STO)
open import Relation.Binary.Isomorphism
open import Relation.Binary.PropositionalEquality

open import Induction.WellFounded

open import Data.FreshList.InductiveInductive as FList
open import Free.IdempotentCommutativeMonoid using (SortedList; insert) renaming (_∈_ to member)

-- Enumerated types are those with a finite enumeration

is-enumeration : (X : Set) (L : List X) → Set
is-enumeration X L = (x : X) → x ∈ L

-- An enumerated type is one where there exists some list
-- L which contains all of the elements of the type.
Enumerated : Set → Set
Enumerated X = ∃[ L ] (is-enumeration X L)

-- A stronger notion of enumeration is to use a sorted list; this ensures canonicity
-- relative to a particular ordering on the type. There's no hope of erasing the proof data,
-- however.
is-strong-enumeration : {X : Set} {_<_ : X → X → Set} (X-STO : IsPropStrictTotalOrder _≡_ _<_) (L : SortedList X-STO) → Set
is-strong-enumeration {X} X-STO L = (x : X) → member X-STO x L

-- nb: this one is proof relevant!
StronglyEnumerated : {X : Set} {_<_ : X → X → Set} (X-STO : IsPropStrictTotalOrder _≡_ _<_) → Set
StronglyEnumerated {X} X-STO = Σ[ L ∈ SortedList X-STO ] is-strong-enumeration X-STO L

---------------
-- Instances --
---------------

private
  enumerate-ℕ : ℕ → SortedList ℕ-STO
  enumerate-ℕ-fresh : (n : ℕ) → n # enumerate-ℕ n
  enumerate-ℕ zero = []
  enumerate-ℕ (suc n) = cons n (enumerate-ℕ n) (enumerate-ℕ-fresh n)
  enumerate-ℕ-fresh zero = []
  enumerate-ℕ-fresh (suc n) = s≤s ≤-refl ∷ #-trans (IsPropStrictTotalOrder.trans ℕ-STO) (suc n) n (enumerate-ℕ n) (s≤s ≤-refl) (enumerate-ℕ-fresh n)

  -- the enumeration is bounded above by n
  enumerate-bounded : ∀ n → All (_< n) (enumerate-ℕ n)
  enumerate-bounded zero = []
  enumerate-bounded (suc n) = (s≤s ≤-refl) ∷ all-map m<n⇒m<1+n (enumerate-bounded n)

  -- so we can inject it into a list of fins
  inject-all : {n : ℕ} (xs : SortedList ℕ-STO) → All (_< n) xs → SortedList (Fin-STO n)
  inject-all-fresh : ∀ {n} {x} {xs} (x#xs : x # xs) (px : x < n) (pxs : All (_< n) xs)
                   → (fromℕ< px) # inject-all xs pxs
  inject-all [] [] = []
  inject-all (cons x xs x#xs) (px ∷ pxs) = cons (fromℕ< px) (inject-all xs pxs) (inject-all-fresh x#xs px pxs)
  inject-all-fresh [] px [] = []
  inject-all-fresh {n} (x ∷ x#xs) px (py ∷ pxs) = fromℕ<-cancel-< py px x ∷ (inject-all-fresh x#xs px pxs)

  enumerate : (n : ℕ) → SortedList (Fin-STO n)
  enumerate n = inject-all (enumerate-ℕ n) (enumerate-bounded n)

  --is-enum-ℕ : (n x : ℕ) → x < n → member ℕ-STO x (enumerate-ℕ n)
  --is-enum-ℕ (suc zero) .zero (s≤s z≤n) = here refl
  --is-enum-ℕ (suc (suc n)) .zero (s≤s z≤n) = {!is-enum-ℕ (suc n) zero ?!}
  --is-enum-ℕ (suc .(suc _)) .(suc _) (s≤s (s≤s p)) = {!!}

  postulate is-enum : ∀ n → is-strong-enumeration (Fin-STO n) (enumerate n)

abstract
  Fin-enum> : ∀ n → StronglyEnumerated (Fin-STO n)
  Fin-enum> n = enumerate n , is-enum n
  -- enumerate-ℕ n = (the list of all nats strictly smaller than n)

  postulate Fin-enum : ∀ n → StronglyEnumerated (Data.Fin.MoreProps.<-isPropStrictTotalOrder n)


{-
Fin-enum : ∀ n → StronglyEnumerated (FinSTO n)
Fin-enum zero = [] , λ ()
Fin-enum (suc n) = enumerate (fromℕ n) (<-wellFounded (toℕ (fromℕ n))) , {!!} where
  enumerate : (m : Fin (suc n)) → Acc _<_ (toℕ m) → SortedList (FinSTO (suc n))
  enumerate-fresh : (m : Fin n) (acc : Acc _<_ (toℕ (inject₁ m))) → fsuc m # enumerate (inject₁ m) acc

  enumerate fzero _ = cons fzero [] []
  enumerate (fsuc m) (acc rs) = cons (fsuc m) (enumerate (inject₁ m) (rs (toℕ (inject₁ m)) (s≤s (≤-reflexive (toℕ-inject₁ m))))) (enumerate-fresh m (rs (toℕ (inject₁ m)) (s≤s (≤-reflexive (toℕ-inject₁ m)))))

  enumerate-fresh fzero (acc rs) = s≤s z≤n ∷ []
  enumerate-fresh (fsuc m) (acc rs) = (s≤s (s≤s {!!})) ∷ {!enumerate-fresh  !}


  is-enum : {! is-strong-enumeration (FinSTO n) (enumerate n) !}
  is-enum = {!!}
-}

{-
-- Another notion of finiteness is when a type is isomorphic to Fin
Finite : Set → Set
Finite X = ∃[ n ] X ≃ Fin n


-- These two notions are isomorphic -- edit: no they're not! the list having duplicates is a problem
Fin→Enum : ∀ X → Finite X → Enumerated X
Fin→Enum X (n , iso) = (enumerate n ≤-refl) , is-enum n ≤-refl where
  enumerate : (m : ℕ) → m ≤ n → List X
  enumerate zero _ = []
  enumerate (suc m) p = from iso (fromℕ< p) ∷ enumerate m (≤-stepL p)

  is-enum : (m : ℕ) → (p : m ≤ n) → is-enumeration X (enumerate m p)
  is-enum zero z≤n x = {!!} -- something is wrong somewhere
  is-enum (suc m) p x = {!!}

-- Add to stdlib under Any.Properties?
lookup-index : {X : Set} (a : X) (xs : List X) → (p : a ∈ xs) → a ≡ lookup xs (index p)
lookup-index a (x ∷ xs) (here  p) = p
lookup-index a (x ∷ xs) (there p) = lookup-index a xs p

index-enum : {X : Set} (xs : List X) (enum : is-enumeration X xs) (i : Fin (length xs)) → i ≡ index (enum (lookup xs i))
index-enum (x ∷ xs) enum fzero = {!enum x!} -- problem: we can see that x is clearly at the head, but there's no guarantee that it isn't duplicated elsewhere.
                                            -- moreover, if x does appear elsewhere in xs, enum may always choose that later occurrence, which we don't want.
                                            -- another use case of sorted lists?
index-enum (x ∷ xs) enum (fsuc i) = {!!}

Enum→Fin : ∀ X → Enumerated X → Finite X
Enum→Fin X (L , enum) = length L , iso where
  iso : X ≃ Fin (length L)
  to iso x = index (enum x)
  from iso x = lookup L x
  from-to iso a = lookup-index a L (enum a)
  to-from iso i = index-enum L enum i

Finite≃Enumerated : ∀ X → Finite X ≃ Enumerated X
Finite≃Enumerated X = {!!}

-- todo: instead of proving the ordering directly like so, it's probably neater to
-- go via the sensible ordering on fins
_<∈_ : {X : Set} {x y : X} {xs : List X} → (x ∈ xs → y ∈ xs → Set)
here  p <∈ here  q = ⊥ -- x=y, so x≮y
here  p <∈ there q = ⊤ -- x<y
there p <∈ here  q = ⊥ -- x>y, so x≮y
there p <∈ there q = p <∈ q

enum⇒ord : ∀ {X L} → is-enumeration X L → (X → X → Set)
enum⇒ord {X} {L} enum x y = (enum x) <∈ (enum y) 

-}
