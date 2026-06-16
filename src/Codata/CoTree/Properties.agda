{-# OPTIONS --safe --guardedness #-}
module Codata.CoTree.Properties where

open import Level using (0ℓ) renaming (suc to lsuc)
open import Data.Product
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Data.LTS.Core
open import Codata.CoTree.Core

private variable
  X : Set

open LTS

-----------------------------
-- The Bisimilarity Setoid --
-----------------------------

mutual
  ~-reflexive : ∀ {xs ys : CoTree X} → xs ≡ ys → xs ~ ys
  head (~-reflexive refl) = refl
  tree (~-reflexive {xs = xs} refl) = ~-reflexive-step (tree xs)
  
  ~-reflexive-step : ∀ (xs : CoTree-step X) → Pointwise-step _≡_ xs xs
  ~-reflexive-step leaf = leaf
  ~-reflexive-step (node1 rs) = node1 (~-reflexive refl)
  ~-reflexive-step (node2 rsl rsr) = node2 (~-reflexive refl) (~-reflexive refl)
  ~-reflexive-step (nodeη rs) = nodeη (~-reflexive refl)


~-refl : ∀ {xs : CoTree X} → xs ~ xs
~-refl {xs = xs} = ~-reflexive {xs = xs} refl

mutual 
  ~-sym : ∀ {xs ys : CoTree X} → xs ~ ys → ys ~ xs
  head (~-sym rs) = sym (head rs)
  tree (~-sym rs) = ~-sym-step (tree rs)

  ~-sym-step : ∀ {xs ys : CoTree-step X} → Pointwise-step _≡_ xs ys → Pointwise-step _≡_ ys xs
  ~-sym-step leaf = leaf
  ~-sym-step (node1 x) = node1 (~-sym x)
  ~-sym-step (node2 x y) = node2 (~-sym x) (~-sym y)
  ~-sym-step (nodeη x) = nodeη (~-sym x)

mutual
  ~-trans : ∀ {xs ys zs : CoTree X} → xs ~ ys → ys ~ zs → xs ~ zs
  head (~-trans rsl rsr) = trans (head rsl) (head rsr)
  tree (~-trans rsl rsr) = ~-trans-step (tree rsl) (tree rsr)
  
  ~-trans-step : ∀ {xs ys zs : CoTree-step X} → Pointwise-step _≡_ xs ys → Pointwise-step _≡_ ys zs → Pointwise-step _≡_ xs zs
  ~-trans-step leaf rsr = rsr
  ~-trans-step (node1 x) (node1 y) = node1 (~-trans x y)
  ~-trans-step (node2 xl xr) (node2 yl yr) = node2 (~-trans xl yl) (~-trans xr yr)
  ~-trans-step (nodeη x) (nodeη y) = nodeη (~-trans x y)

~-isEquivalence : IsEquivalence (_~_ {X})
IsEquivalence.refl ~-isEquivalence = ~-refl
IsEquivalence.sym ~-isEquivalence p = ~-sym p
IsEquivalence.trans ~-isEquivalence p q = ~-trans p q

~-Setoid : Set → Setoid 0ℓ 0ℓ
Setoid.Carrier (~-Setoid X) = CoTree X
Setoid._≈_ (~-Setoid X) = _~_
Setoid.isEquivalence (~-Setoid X) = ~-isEquivalence

module bisim-Reasoning X = pw-Reasoning (setoid X)

------------------------------
-- Interpretation as an LTS --
------------------------------

-- The labels will be the node arities.
-- There is no label for leaves, since they don't have successors.
data Arity : Set where
  lf n1 n2ₗ n2ᵣ nη : Arity

-- The labelled transition relation; it picks out the appropriate
-- successor for the label, up to pointwise equality.
data IsSuccessor' {X : Set} : CoTree-step X → Arity → CoTree X → Set where
  node1 : ∀ {s t} → Pointwise-step _≡_ s (node1 t) → IsSuccessor' s n1 t
  node2ₗ : ∀ {s tl tr} → Pointwise-step _≡_ s (node2 tl tr) → IsSuccessor' s n2ₗ tl
  node2ᵣ : ∀ {s tl tr} → Pointwise-step _≡_ s (node2 tl tr) → IsSuccessor' s n2ᵣ tr
  nodeη : ∀ {s t} → Pointwise-step _≡_ s (nodeη t) → IsSuccessor' s nη t


IsSuccessor : {X : Set} → CoTree X → Arity → CoTree X → Set
IsSuccessor s l t = IsSuccessor' (s .tree) l t
  


-- We can interpret the entire type of cotrees for any X as an LTS.
-- We could have even intepreted the fibration of cotrees bundled with their
-- parameter X, but then we'd have needed to consider equality of heads up to an  
-- isomorphism of the parameter types; this easier notion suffices.
-- 
-- The states are the cotrees themselves, and there is a transition `s -[l]-> t`
-- if t is exactly the successor of s in direction l. 
CoTree-LTS : (X : Set) → LTS 0ℓ 0ℓ 0ℓ
CoTree-LTS X .State = CoTree X
CoTree-LTS X .Label = Arity
CoTree-LTS X ._-[_]->_ = IsSuccessor

-- The identity type is a bisimulation of this LTS
≡-is-bisimulation : ∀ {X} → IsBisimulation (CoTree-LTS X) _≡_
≡-is-bisimulation {p = p} {q = .p} refl l .proj₁ {p'} p→p' = p' , p→p' , refl
≡-is-bisimulation {p = p} {q = .p} refl l .proj₂ {q'} p→q' = q' , p→q' , refl

-- The pointwise lifting of equality is a bisimulation of this LTS
~-is-bisimulation : ∀ {X} → IsBisimulation (CoTree-LTS X) _~_
~-is-bisimulation p~q l .proj₁ (node1 x) = _ , node1 (~-trans-step ((~-sym p~q) .tree) x) , ~-refl
~-is-bisimulation p~q l .proj₁ (node2ₗ x) = _ , node2ₗ (~-trans-step ((~-sym p~q) .tree) x) , ~-refl
~-is-bisimulation p~q l .proj₁ (node2ᵣ x) = _ , node2ᵣ (~-trans-step ((~-sym p~q) .tree) x) , ~-refl
~-is-bisimulation p~q l .proj₁ (nodeη x) = _ , nodeη (~-trans-step ((~-sym p~q) .tree) x) , ~-refl
~-is-bisimulation p~q l .proj₂ (node1 x) = _ , node1 (~-trans-step (p~q .tree) x) , ~-refl
~-is-bisimulation p~q l .proj₂ (node2ₗ x) =  _ , node2ₗ (~-trans-step (p~q .tree) x) , ~-refl
~-is-bisimulation p~q l .proj₂ (node2ᵣ x) = _ , node2ᵣ (~-trans-step (p~q .tree) x) , ~-refl
~-is-bisimulation p~q l .proj₂ (nodeη x) = _ , nodeη (~-trans-step (p~q .tree) x) , ~-refl

----------------------------------------
-- A Different Notion of Bisimilarity --
----------------------------------------

data SameArity' {X : Set} : CoTree-step X → CoTree-step X → Set where
  leaf : SameArity' leaf leaf
  node1 : ∀ s t → SameArity' (node1 s) (node1 t)
  node2 : ∀ sl sr tl tr → SameArity' (node2 sl sr) (node2 tl tr)
  nodeη : ∀ s t → SameArity' (nodeη s) (nodeη t)

SameArity : {X : Set} → CoTree X → CoTree X → Set
SameArity s t = SameArity' (s .tree) (t .tree)


-- They coincide:

------------------
-- Bisimilarity --
------------------

{-

-- And it's the maximal bisimulation:
~-greatest-bisimulation : ∀ {X} {R : CoTree X → CoTree X → Set}
                        → IsBisimulation (CoTree-LTS X) R
                        → (∀ {s t : CoTree X} → R s t → s ~ t)
~-greatest-bisimulation {R = R} bisim Rst .head = ?
~-greatest-bisimulation {R = R} bisim Rst .tree = {!!}

-- And thus, pointwise lifting of equality really is bisimilarity of cotrees.
~-is-bisimilarity : ∀ {X} → IsBisimilarity (CoTree-LTS X) _~_
~-is-bisimilarity p q .Equivalence.to p~q = _~_ , ~-is-bisimulation , p~q
~-is-bisimilarity p q .Equivalence.from (R , R-bisim , Rpq) = {!!}
~-is-bisimilarity p q .Equivalence.to-cong = {!!}
~-is-bisimilarity p q .Equivalence.from-cong = {!!}

-}
