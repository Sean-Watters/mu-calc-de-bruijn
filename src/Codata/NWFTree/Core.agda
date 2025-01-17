{-# OPTIONS --guardedness #-}
module Codata.NWFTree.Core where

open import Level using (0ℓ)
open import Function using (id)
open import Relation.Binary.PropositionalEquality
open import MuCalc.DeBruijn.Base
open import Relation.Binary.Bundles using (Setoid)

private variable
  X : Set

-- A type of nonwellfounded trees with nodes labelled
-- by ■/◆/∧/∨/μ/μ, storing data at both leaves and nodes

record ∞NWFTree (X : Set) : Set
data NWFTree (X : Set) : Set

record ∞NWFTree X where
  coinductive
  field
    head : X -- we factor this out, rather that duplicating it between every constructor
    tree : NWFTree X
open ∞NWFTree public

data NWFTree X where
  leaf : NWFTree X
  node1 : Op₁ → ∞NWFTree X → NWFTree X
  node2 : Op₂ → ∞NWFTree X → ∞NWFTree X → NWFTree X
  nodeη : Opη → ∞NWFTree X → NWFTree X


-- P eventually becomes true (in finitely many steps)
data Eventually {X : Set} (P : X → Set) (t : ∞NWFTree X) : Set
data Eventually-step {X : Set} (P : X → Set) : NWFTree X → Set

data Eventually P t where
  here : P (head t) → Eventually P t
  there : Eventually-step P (tree t) → Eventually P t

data Eventually-step P where
  node1  : ∀ {op t}   → Eventually P t → Eventually-step P (node1 op t)
  node2l : ∀ {op l r} → Eventually P l → Eventually-step P (node2 op l r)
  node2r : ∀ {op l r} → Eventually P r → Eventually-step P (node2 op l r)
  nodeη  : ∀ {op t}   → Eventually P t → Eventually-step P (nodeη op t)

-- x ∈ t, for a nwf tree `t`
_∈_ : X → ∞NWFTree X → Set
x ∈ t = Eventually (x ≡_) t

-------------------------------
-- Bisimilarity of NWF Trees --
-------------------------------

-- Pointwise lifting of relations to trees
record ∞Pointwise {X : Set} (R : X → X → Set) (s t : ∞NWFTree X) : Set
data Pointwise {X : Set} (R : X → X → Set) : (s t : NWFTree X) → Set

record ∞Pointwise R s t where
  coinductive
  field
    head : R (head s) (head t)
    tree : Pointwise R (tree s) (tree t)
open ∞Pointwise public

data Pointwise R where
  leaf : Pointwise R leaf leaf
  node1 : ∀ {op op' s t} → ∞Pointwise R s t → Pointwise R (node1 op s) (node1 op' t)
  node2 : ∀ {op op' sl sr tl tr} → ∞Pointwise R sl tl → ∞Pointwise R sr tr → Pointwise R (node2 op sl sr) (node2 op' tl tr)
  nodeη : ∀ {op op' s t} → ∞Pointwise R s t → Pointwise R (nodeη op s) (nodeη op' t)


-- Bisim is pointwise ≡
_~_ :  ∞NWFTree X → ∞NWFTree X → Set
s ~ t = ∞Pointwise _≡_ s t

-- Bisimilarity Extensionality.
-- True in OTT and HoTT(?), but not plain MLTT.
-- We may at some point need to postulate this.
BisimExt : Set → Set
BisimExt X = ∀ {s t : ∞NWFTree X} → s ~ t → s ≡ t


------------------------------------------------------------------------
-- Equational Reasoning for Bisimilarity
--
-- Based on `Codata.Guarded.Stream.Relation.Binary.Pointwise` in the
-- standard library for streams, which in turn is based on Nils Anders
-- Danielsson's "Beating the Productivity Checker Using Embedded Languages"

module pw-Reasoning (S : Setoid 0ℓ 0ℓ) where
  private module S = Setoid S
  open S using (_≈_) renaming (Carrier to C)

  record `∞Pointwise     (s t : ∞NWFTree C) : Set
  data   `Pointwise    : (s t : NWFTree C) → Set
  data   `PointwiseProof (s t : ∞NWFTree C) : Set

  record `∞Pointwise s t where
    coinductive
    field
      head : (head s) ≈ (head t)
      tree : `Pointwise (tree s) (tree t)
  open `∞Pointwise public

  data `Pointwise where
    leaf : `Pointwise leaf leaf
    node1 : ∀ {op op' s t} → `PointwiseProof s t → `Pointwise (node1 op s) (node1 op' t)
    node2 : ∀ {op op' sl sr tl tr} → `PointwiseProof sl tl → `PointwiseProof sr tr → `Pointwise (node2 op sl sr) (node2 op' tl tr)
    nodeη : ∀ {op op' s t} → `PointwiseProof s t → `Pointwise (nodeη op s) (nodeη op' t)

  data `PointwiseProof s t where
    `lift  : (rs : ∞Pointwise _≈_ s t) → `PointwiseProof s t
    `bisim : (rs : s ~ t) → `PointwiseProof s t
    `refl  : (eq : s ≡ t) → `PointwiseProof s t
    `step  : (`rs : `∞Pointwise s t) → `PointwiseProof s t
    `sym   : (`rs : `PointwiseProof t s) → `PointwiseProof s t
    `trans : ∀ {i} → (`rsl : `PointwiseProof s i) → (`rsr : `PointwiseProof i t) → `PointwiseProof s t


  `map-lift : ∀ {s t} → Pointwise _≈_ s t → `Pointwise s t
  `map-lift leaf = leaf
  `map-lift (node1 x) = node1 (`lift x)
  `map-lift (node2 x y) = node2 (`lift x) (`lift y)
  `map-lift (nodeη x) = nodeη (`lift x)

  `map-bisim : ∀ {s t} → Pointwise _≡_ s t → `Pointwise s t
  `map-bisim leaf = leaf
  `map-bisim (node1 x) = node1 (`bisim x)
  `map-bisim (node2 x y) = node2 (`bisim x) (`bisim y)
  `map-bisim (nodeη x) = nodeη (`bisim x)

  `map-refl : ∀ {s t} → s ≡ t → `Pointwise s t
  `map-refl {leaf} refl = leaf
  `map-refl {node1 _ _} refl = node1 (`refl refl)
  `map-refl {node2 _ _ _} refl = node2 (`refl refl) (`refl refl)
  `map-refl {nodeη _ _} refl = nodeη (`refl refl)

  `map-sym : ∀ {s t} → `Pointwise t s → `Pointwise s t
  `map-sym leaf = leaf
  `map-sym (node1 x) = node1 (`sym x)
  `map-sym (node2 x y) = node2 (`sym x) (`sym y)
  `map-sym (nodeη x) = nodeη (`sym x)

  `map-trans : ∀ {s i t} → `Pointwise s i → `Pointwise i t → `Pointwise s t
  `map-trans leaf leaf = leaf
  `map-trans (node1 x) (node1 y) = node1 (`trans x y)
  `map-trans (node2 x y) (node2 u v) = node2 (`trans x u) (`trans y v)
  `map-trans (nodeη x) (nodeη y) = nodeη (`trans x y)

  `head : ∀ {s t} → `PointwiseProof s t → (head s) ≈ (head t)
  `head (`lift rs) = head rs
  `head (`bisim rs) = S.reflexive (head rs)
  `head (`refl eq) = S.reflexive (cong head eq)
  `head (`step `rs) = head `rs
  `head (`sym `rs) = S.sym (`head `rs)
  `head (`trans `rsl `rsr) = S.trans (`head `rsl) (`head `rsr)

  `tree : ∀ {s t} → `PointwiseProof s t → `Pointwise (tree s) (tree t)
  `tree (`lift rs) = `map-lift (tree rs)
  `tree (`bisim rs) = `map-bisim (tree rs)
  `tree (`refl eq) = `map-refl (cong tree eq)
  `tree (`step `rs) = tree `rs
  `tree (`sym `rs) = `map-sym (`tree `rs)
  `tree (`trans `rsl `rsr) = `map-trans (`tree `rsl) (`tree `rsr)

  run : ∀ {s t} → `PointwiseProof s t → ∞Pointwise _≈_ s t
  run-tree : ∀ {s t} → `Pointwise s t → Pointwise _≈_ s t

  head (run `rs) = `head `rs
  tree (run `rs) = run-tree (`tree `rs)

  run-tree leaf = leaf
  run-tree (node1 x) = node1 (run x)
  run-tree (node2 x y) = node2 (run x) (run y)
  run-tree (nodeη x) = nodeη (run x)
