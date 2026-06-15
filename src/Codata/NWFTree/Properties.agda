{-# OPTIONS --safe --guardedness #-}
module Codata.NWFTree.Properties where

open import Level using (0ℓ) renaming (suc to lsuc)
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Data.LTS.Core
open import Codata.NWFTree.Core
open import MuCalc.Base

private variable
  X : Set

open LTS

------------------------------
-- Interpretation as an LTS --
------------------------------

{-

-- The labels will be the node arities.
-- There is no label for leaves, since they don't have successors.
data Arity : Set where
  n1 n2ₗ n2ᵣ nη : Arity

-- The labelled transition relation;
data IsSuccessor (X : Set) : ∞NWFTree X → Arity → ∞NWFTree X → Set
  node1 : IsSuccessor (x ∷ (node1 op s))

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
∞NWFTree-LTS X ._-[_]->_ xs l ys = {!xs .subtree!}

-}

-----------------------------
-- The Bisimilarity Setoid --
-----------------------------

~-reflexive : ∀ {xs ys : ∞NWFTree X} → xs ≡ ys → xs ~ ys
head (~-reflexive refl) = refl
tree (~-reflexive {xs = xs} refl) with tree xs
... | leaf = leaf
... | node1 op rs = node1 (~-reflexive refl)
... | node2 op rsl rsr = node2 (~-reflexive refl) (~-reflexive refl)
... | nodeη op rs = nodeη (~-reflexive refl)


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
