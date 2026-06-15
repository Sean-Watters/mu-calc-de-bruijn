{-# OPTIONS --safe --guardedness #-}
module Codata.NWFTree.Properties where

open import Level using (0ℓ) renaming (suc to lsuc)
open import Data.Product
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Data.LTS.Core
open import Codata.NWFTree.Core
open import MuCalc.Base

private variable
  X : Set

open LTS

-----------------------------
-- The Bisimilarity Setoid --
-----------------------------

~-reflexive : ∀ {xs ys : ∞NWFTree X} → xs ≡ ys → xs ~ ys
head (~-reflexive refl) = refl
tree (~-reflexive {xs = xs} refl) with tree xs
... | leaf = leaf
... | node1 rs = node1 (~-reflexive refl)
... | node2 rsl rsr = node2 (~-reflexive refl) (~-reflexive refl)
... | nodeη rs = nodeη (~-reflexive refl)


~-refl : ∀ (xs : ∞NWFTree X) → xs ~ xs
~-refl xs = ~-reflexive {xs = xs} refl

~-sym : ∀ {xs ys : ∞NWFTree X} → xs ~ ys → ys ~ xs
head (~-sym rs) = sym (head rs)
tree (~-sym {xs = xs} {ys} rs) with tree xs | tree ys | tree rs
... | _ | _ | leaf = leaf
... | _ | _ | node1 x = node1 (~-sym x)
... | _ | _ | node2 x y = node2 (~-sym x) (~-sym y)
... | _ | _ | nodeη x = nodeη (~-sym x)

~-trans : ∀ {xs ys zs : ∞NWFTree X} → xs ~ ys → ys ~ zs → xs ~ zs
head (~-trans rsl rsr) = trans (head rsl) (head rsr)
tree (~-trans {xs = xs} {ys} {zs} rsl rsr) with tree xs | tree ys | tree zs | tree rsl | tree rsr
... | _ | _ | _ | leaf | v = v
... | _ | _ | _ | node1 x | node1 y = node1 (~-trans x y)
... | _ | _ | _ | node2 x u | node2 y v = node2 (~-trans x y) (~-trans u v)
... | _ | _ | _ | nodeη x | nodeη y = nodeη (~-trans x y)

~-isEquivalence : IsEquivalence (_~_ {X})
IsEquivalence.refl ~-isEquivalence {x} = ~-refl x
IsEquivalence.sym ~-isEquivalence p = ~-sym p
IsEquivalence.trans ~-isEquivalence p q = ~-trans p q

~-Setoid : Set → Setoid 0ℓ 0ℓ
Setoid.Carrier (~-Setoid X) = ∞NWFTree X
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
data IsSuccessor' {X : Set} : NWFTree X → Arity → ∞NWFTree X → Set where
  node1 : ∀ {s t} → Pointwise _≡_ s (node1 t) → IsSuccessor' s n1 t
  node2ₗ : ∀ {s tl tr} → Pointwise _≡_ s (node2 tl tr) → IsSuccessor' s n2ₗ tl
  node2ᵣ : ∀ {s tl tr} → Pointwise _≡_ s (node2 tl tr) → IsSuccessor' s n2ᵣ tr
  nodeη : ∀ {s t} → Pointwise _≡_ s (nodeη t) → IsSuccessor' s nη t


IsSuccessor : {X : Set} → ∞NWFTree X → Arity → ∞NWFTree X → Set
IsSuccessor s l t = IsSuccessor' (s .tree) l t
  


-- We can interpret the entire type of cotrees for any X as an LTS.
-- We could have even intepreted the fibration of cotrees bundled with their parameter
-- X, but then we'd have needed to consider equality of heads up to an isomorphism of the
-- parameter types; this easier notion suffices.
-- 
-- The states are the cotrees themselves, and there is a transition `s -[l]-> t` if t is exactly
-- the successor of s in direction l. 
∞NWFTree-LTS : (X : Set) → LTS 0ℓ 0ℓ 0ℓ
∞NWFTree-LTS X .State = ∞NWFTree X
∞NWFTree-LTS X .Label = Arity
∞NWFTree-LTS X ._-[_]->_ = IsSuccessor

-- The identity type is a bisimulation of this LTS
≡-is-bisimulation : ∀ {X} → IsBisimulation (∞NWFTree-LTS X) _≡_
≡-is-bisimulation {p = p} {q = .p} refl l .proj₁ {p'} p→p' = p' , p→p' , refl
≡-is-bisimulation {p = p} {q = .p} refl l .proj₂ {q'} p→q' = q' , p→q' , refl

-- The pointwise lifting of equality is a bisimulation of this LTS
~-is-bisimulation : ∀ {X} → IsBisimulation (∞NWFTree-LTS X) _~_
~-is-bisimulation p~q l .proj₁ (node1 x) = {!!}
~-is-bisimulation p~q l .proj₁ (node2ₗ x) = {!!}
~-is-bisimulation p~q l .proj₁ (node2ᵣ x) = {!!}
~-is-bisimulation p~q l .proj₁ (nodeη x) = {!!}
~-is-bisimulation p~q l .proj₂ = {!!}

-- ~-is-bisimulation : ∀ {X} → IsBisimulation (∞NWFTree-LTS X) _~_
-- ~-is-bisimulation p~q l .proj₁ (node1 x) = _ , node1 (~-trans (~-sym p~q) x) , ~-refl _
-- ~-is-bisimulation p~q l .proj₁ (node2ₗ x) = _ , node2ₗ (~-trans (~-sym p~q) x) , ~-refl _ 
-- ~-is-bisimulation p~q l .proj₁ (node2ᵣ x) = _ , node2ᵣ (~-trans (~-sym p~q) x) , ~-refl _ 
-- ~-is-bisimulation p~q l .proj₁ (nodeη x)  = _ , nodeη  (~-trans (~-sym p~q) x) , ~-refl _ 
-- ~-is-bisimulation p~q l .proj₂ (node1 x) = _ , node1 (~-trans p~q x) , ~-refl _
-- ~-is-bisimulation p~q l .proj₂ (node2ₗ x) = _ , node2ₗ (~-trans p~q x) , ~-refl _ 
-- ~-is-bisimulation p~q l .proj₂ (node2ᵣ x) = _ , node2ᵣ (~-trans p~q x) , ~-refl _ 
-- ~-is-bisimulation p~q l .proj₂ (nodeη x)  = _ , nodeη  (~-trans p~q x) , ~-refl _ 

{-
data SameArity' {X : Set} : NWFTree X → NWFTree X → Set where
  leaf : SameArity' leaf leaf
  node1 : ∀ s t → SameArity' (node1 s) (node1 t)
  node2 : ∀ sl sr tl tr → SameArity' (node2 sl sr) (node2 tl tr)
  nodeη : ∀ s t → SameArity' (nodeη s) (nodeη t)

SameArity : {X : Set} → ∞NWFTree X → ∞NWFTree X → Set
SameArity s t = SameArity' (s .tree) (t .tree)

-- If two trees are similar, they must have the same arity
bisim⇒SameArity : ∀ {X} {R : ∞NWFTree X → ∞NWFTree X → Set}
              → IsBisimulation (∞NWFTree-LTS X) R
              → (∀ (s t : ∞NWFTree X) → R s t → SameArity s t)
bisim⇒SameArity bisim s t Rst with s .tree in eq
... | leaf = {!!}
... | node1 x = {!bisim Rst n1 .proj₁ (node1 ?)!}
... | node2 x x₁ = {!!}
... | nodeη x = {!!}

{-

-- If two trees are bisimilar, then their heads are equal
bisim⇒eq-head : ∀ {X} {R : ∞NWFTree X → ∞NWFTree X → Set}
              → IsBisimulation (∞NWFTree-LTS X) R
              → (∀ {s t : ∞NWFTree X} → R s t → s .head ≡ t .head)
bisim⇒eq-head (sim , sim-op) {s} {t} Rst = {!sim Rst!}

-- And it's the maximal bisimulation:
~-greatest-bisimulation : ∀ {X} {R : ∞NWFTree X → ∞NWFTree X → Set}
                        → IsBisimulation (∞NWFTree-LTS X) R
                        → (∀ {s t : ∞NWFTree X} → R s t → s ~ t)
~-greatest-bisimulation {R = R} (sim , sim-flip) {s} {t} Rst .head
  = {!sim!}
~-greatest-bisimulation {R = R} (sim , sim-flip) Rst .tree = {!!}

-- And thus, pointwise lifting of equality really is bisimilarity of cotrees.
~-is-bisimilarity : ∀ {X} → IsBisimilarity (∞NWFTree-LTS X) _~_
~-is-bisimilarity p q .Equivalence.to p~q = _~_ , ~-is-bisimulation , p~q
~-is-bisimilarity p q .Equivalence.from (R , R-bisim , Rpq) = {!!}
~-is-bisimilarity p q .Equivalence.to-cong = {!!}
~-is-bisimilarity p q .Equivalence.from-cong = {!!}

-}
-}
