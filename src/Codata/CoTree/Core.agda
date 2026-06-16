{-# OPTIONS --safe --guardedness #-}
module Codata.CoTree.Core where

open import Level using (0ℓ)
open import Function using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import MuCalc.Base
open import Relation.Binary.Bundles using (Setoid)

private variable
  X : Set

-- A type of nonwellfounded trees with nodes labelled
-- by ■/◆/∧/∨/μ/ν, storing data at both leaves and nodes

record CoTree (X : Set) : Set
data CoTree-step (X : Set) : Set

record CoTree X where
  constructor _∷_
  coinductive
  field
    head : X -- we factor this out, rather that duplicating it between every constructor
    tree : CoTree-step X
open CoTree public

data CoTree-step X where
  leaf : CoTree-step X
  node1 : CoTree X → CoTree-step X
  node2 : CoTree X → CoTree X → CoTree-step X
  nodeη : CoTree X → CoTree-step X


-- P possibly becomes true (in finitely many steps). AKA there is a path through the tree
-- to an element that satisfies P
data Any {X : Set} (P : X → Set) (t : CoTree X) : Set
data Any-step {X : Set} (P : X → Set) : CoTree-step X → Set

data Any P t where
  here : P (head t) → Any P t
  there : Any-step P (tree t) → Any P t

data Any-step P where
  node1  : ∀ {t}   → Any P t → Any-step P (node1 t)
  node2l : ∀ {l r} → Any P l → Any-step P (node2 l r)
  node2r : ∀ {l r} → Any P r → Any-step P (node2 l r)
  nodeη  : ∀ {t}   → Any P t → Any-step P (nodeη t)

-- x ∈ t, for a nwf tree `t`
_∈_ : X → CoTree X → Set
x ∈ t = Any (x ≡_) t

-------------------------------
-- Bisimilarity of NWF Trees --
-------------------------------

-- Pointwise-step lifting of relations to trees
record Pointwise {X : Set} (R : X → X → Set) (s t : CoTree X) : Set
data Pointwise-step {X : Set} (R : X → X → Set) : (s t : CoTree-step X) → Set

record Pointwise R s t where
  constructor _∷_
  coinductive
  field
    head : R (head s) (head t)
    tree : Pointwise-step R (tree s) (tree t)
open Pointwise public

data Pointwise-step R where
  leaf : Pointwise-step R leaf leaf
  node1 : ∀ {s t} → Pointwise R s t → Pointwise-step R (node1 s) (node1 t)
  node2 : ∀ {sl sr tl tr} → Pointwise R sl tl → Pointwise R sr tr → Pointwise-step R (node2 sl sr) (node2 tl tr)
  nodeη : ∀ {s t} → Pointwise R s t → Pointwise-step R (nodeη s) (nodeη t)


-- Bisim is pointwise ≡
_~_ :  CoTree X → CoTree X → Set
s ~ t = Pointwise _≡_ s t

-- Bisimilarity Extensionality.
BisimExt : Set → Set
BisimExt X = ∀ {s t : CoTree X} → s ~ t → s ≡ t


------------------------------------------------------------------------
-- Equational Reasoning for Bisimilarity
--
-- Based on `Codata.Guarded.Stream.Relation.Binary.Pointwise` in the
-- standard library for streams, which in turn is based on Nils Anders
-- Danielsson's "Beating the Productivity Checker Using Embedded Languages"

module pw-Reasoning (S : Setoid 0ℓ 0ℓ) where
  private module S = Setoid S
  open S using (_≈_) renaming (Carrier to C)

  record `Pointwise     (s t : CoTree C) : Set
  data   `Pointwise-step    : (s t : CoTree-step C) → Set
  data   `PointwiseProof (s t : CoTree C) : Set

  record `Pointwise s t where
    coinductive
    field
      head : (head s) ≈ (head t)
      tree : `Pointwise-step (tree s) (tree t)
  open `Pointwise public

  data `Pointwise-step where
    leaf : `Pointwise-step leaf leaf
    node1 : ∀ {s t} → `PointwiseProof s t → `Pointwise-step (node1 s) (node1 t)
    node2 : ∀ {sl sr tl tr} → `PointwiseProof sl tl → `PointwiseProof sr tr → `Pointwise-step (node2 sl sr) (node2  tl tr)
    nodeη : ∀ {s t} → `PointwiseProof s t → `Pointwise-step (nodeη s) (nodeη  t)

  data `PointwiseProof s t where
    `lift  : (rs : Pointwise _≈_ s t) → `PointwiseProof s t
    `bisim : (rs : s ~ t) → `PointwiseProof s t
    `refl  : (eq : s ≡ t) → `PointwiseProof s t
    `step  : (`rs : `Pointwise s t) → `PointwiseProof s t
    `sym   : (`rs : `PointwiseProof t s) → `PointwiseProof s t
    `trans : ∀ {i} → (`rsl : `PointwiseProof s i) → (`rsr : `PointwiseProof i t) → `PointwiseProof s t


  `map-lift : ∀ {s t} → Pointwise-step _≈_ s t → `Pointwise-step s t
  `map-lift leaf = leaf
  `map-lift (node1 x) = node1 (`lift x)
  `map-lift (node2 x y) = node2 (`lift x) (`lift y)
  `map-lift (nodeη x) = nodeη (`lift x)

  `map-bisim : ∀ {s t} → Pointwise-step _≡_ s t → `Pointwise-step s t
  `map-bisim leaf = leaf
  `map-bisim (node1 x) = node1 (`bisim x)
  `map-bisim (node2 x y) = node2 (`bisim x) (`bisim y)
  `map-bisim (nodeη x) = nodeη (`bisim x)

  `map-refl : ∀ {s t} → s ≡ t → `Pointwise-step s t
  `map-refl {leaf} refl = leaf
  `map-refl {node1 _} refl = node1 (`refl refl)
  `map-refl {node2 _ _} refl = node2 (`refl refl) (`refl refl)
  `map-refl {nodeη _} refl = nodeη (`refl refl)

  `map-sym : ∀ {s t} → `Pointwise-step t s → `Pointwise-step s t
  `map-sym leaf = leaf
  `map-sym (node1 x) = node1 (`sym x)
  `map-sym (node2 x y) = node2 (`sym x) (`sym y)
  `map-sym (nodeη x) = nodeη (`sym x)

  `map-trans : ∀ {s i t} → `Pointwise-step s i → `Pointwise-step i t → `Pointwise-step s t
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

  `tree : ∀ {s t} → `PointwiseProof s t → `Pointwise-step (tree s) (tree t)
  `tree (`lift rs) = `map-lift (tree rs)
  `tree (`bisim rs) = `map-bisim (tree rs)
  `tree (`refl eq) = `map-refl (cong tree eq)
  `tree (`step `rs) = tree `rs
  `tree (`sym `rs) = `map-sym (`tree `rs)
  `tree (`trans `rsl `rsr) = `map-trans (`tree `rsl) (`tree `rsr)

  run : ∀ {s t} → `PointwiseProof s t → Pointwise _≈_ s t
  run-tree : ∀ {s t} → `Pointwise-step s t → Pointwise-step _≈_ s t

  head (run `rs) = `head `rs
  tree (run `rs) = run-tree (`tree `rs)

  run-tree leaf = leaf
  run-tree (node1 x) = node1 (run x)
  run-tree (node2 x y) = node2 (run x) (run y)
  run-tree (nodeη x) = nodeη (run x)

  -- The equational reasoning syntax --

  begin_ : ∀ {s t} → `PointwiseProof s t → Pointwise _≈_ s t
  begin_ = run

  pattern _↺⟨_⟩_ s s∼t t∼u = `trans {s = s} (`step s∼t) t∼u
  pattern _↺⟨_⟨_ s t∼s t∼u = `trans {s = s} (`sym (`step t∼s)) t∼u
  pattern _~⟨_⟩_ s s∼t t∼u = `trans {s = s} (`lift s∼t) t∼u
  pattern _~⟨_⟨_ s t∼s t∼u = `trans {s = s} (`sym (`lift t∼s)) t∼u
  pattern _≈⟨_⟩_ s s∼t t∼u = `trans {s = s} (`bisim s∼t) t∼u
  pattern _≈⟨_⟨_ s t∼s t∼u = `trans {s = s} (`sym (`bisim t∼s)) t∼u
  pattern _≡⟨_⟩_ s s∼t t∼u = `trans {s = s} (`refl s∼t) t∼u
  pattern _≡⟨_⟨_ s t∼s t∼u = `trans {s = s} (`sym (`refl t∼s)) t∼u
  pattern _≡⟨⟩_  s s∼t     = `trans {s = s} (`refl refl) s∼t
  pattern _∎    s          = `refl  {s = s} refl

  infix  1 begin_
  infixr 2 _↺⟨_⟩_ _↺⟨_⟨_ _~⟨_⟩_ _~⟨_⟨_ _≈⟨_⟩_ _≈⟨_⟨_ _≡⟨_⟩_ _≡⟨_⟨_ _≡⟨⟩_
  infix  3 _∎


