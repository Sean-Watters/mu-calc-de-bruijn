{-# OPTIONS --guardedness #-}
module Codata.NWFTree.Properties where

open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Codata.NWFTree.Core
open import MuCalc.DeBruijn.Base

--------------------------------
-- Properties of Bisimilarity --
--------------------------------

~-reflexive : ∀ {X} {xs ys : ∞NWFTree X} → xs ≡ ys → xs ~ ys
force (~-reflexive {xs = xs} refl) with force xs
... | leaf x = leaf refl
... | node1 op x s = node1 refl (~-reflexive {xs = s} refl)
... | node2 op x s t = node2 refl (~-reflexive {xs = s} refl) (~-reflexive {xs = t} refl)
... | nodeη op x s = nodeη refl (~-reflexive {xs = s} refl)

~-refl : ∀ {X} (xs : ∞NWFTree X) → xs ~ xs
~-refl xs = ~-reflexive {xs = xs} refl

~-sym : ∀ {X} {xs ys : ∞NWFTree X} → xs ~ ys → ys ~ xs
force (~-sym {X} {xs} {ys} b) with force ys | force xs | force b
... | .(leaf _) | .(leaf _) | leaf p = leaf (sym p)
... | (node1 _ _ s) | (node1 _ _ t) | node1 p q = node1 (sym p) (~-sym {X} {t} {s} q)
... | (node2 _ _ sl sr) | (node2 _ _ tl tr) | node2 p q r = node2 (sym p) (~-sym {X} {tl} {sl} q) (~-sym {X} {tr} {sr} r)
... | (nodeη _ _ s) | (nodeη _ _ t) | nodeη p q = nodeη (sym p) (~-sym {X} {t} {s} q)

~-trans : ∀ {X} {xs ys zs : ∞NWFTree X} → xs ~ ys → ys ~ zs → xs ~ zs
force (~-trans {X} {xs} {ys} {zs} bl br) with force xs | force ys | force zs | force bl | force br
... | (leaf _) | (leaf _) | c | leaf p | leaf p' = leaf (trans p p')
... | (node1 _ _ s) | (node1 _ _ t) | (node1 _ _ u) | node1 p q | node1 p' q'
  = node1 (trans p p') (~-trans {X} {s} {t} {u} q q')
... | (node2 _ _ sl sr) | (node2 _ _ tl tr) | (node2 _ _ ul ur) | node2 p q r | node2 p' q' r'
  = node2 (trans p p') (~-trans {X} {sl} {tl} {ul} q q') (~-trans {X} {sr} {tr} {ur} r r')
... | (nodeη _ _ s) | (nodeη _ _ t) | (nodeη _ _ u) | nodeη p q | nodeη p' q'
  = nodeη (trans p p') (~-trans {X} {s} {t} {u} q q')

~-isEquivalence : ∀ {X} → IsEquivalence (_~_ {X})
IsEquivalence.refl (~-isEquivalence {X}) {x} = ~-refl x
IsEquivalence.sym (~-isEquivalence {X}) {x} {y} p = ~-sym {X} {x} {y} p
IsEquivalence.trans (~-isEquivalence {X}) = {!!}


