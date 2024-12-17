{-# OPTIONS --guardedness #-}
module Codata.NWFTree where

open import Relation.Binary.PropositionalEquality
open import MuCalc.DeBruijn.Base

-- A type of nonwellfounded trees with nodes labelled
-- by ■/◆/∧/∨/μ/μ, storing data at both leaves and nodes

record ∞NWFTree (X : Set) : Set
data NWFTree (X : Set) : Set

record ∞NWFTree X where
  coinductive
  field force : NWFTree X
open ∞NWFTree public

data NWFTree X where
  leaf : X → NWFTree X
  node1 : Op₁ → X → ∞NWFTree X → NWFTree X
  node2 : Op₂ → X → ∞NWFTree X → ∞NWFTree X → NWFTree X
  nodeη : Opη → X → ∞NWFTree X → NWFTree X

-- P eventually becomes true (in finitely many steps)
data Eventually {X : Set} (P : X → Set) : NWFTree X → Set where
  herel : ∀ {x} → P x → Eventually P (leaf x)
  here1 : ∀ {op x t} → P x → Eventually P (node1 op x t)
  there1 : ∀ {op x t} → Eventually P (force t) → Eventually P (node1 op x t)
  here2 : ∀ {op x l r} → P x → Eventually P (node2 op x l r)
  there2l : ∀ {op x l r} → Eventually P (force l) → Eventually P (node2 op x l r)
  there2r : ∀ {op x l r} → Eventually P (force r) → Eventually P (node2 op x l r)
  hereη : ∀ {op x t} → P x → Eventually P (nodeη op x t)
  thereη : ∀ {op x t} → Eventually P (force t) → Eventually P (nodeη op x t)

-- x ∈ t, for a nwf tree `t`
_∈T_ : {X : Set} → X → ∞NWFTree X → Set
x ∈T t = Eventually (x ≡_) (force t)

-------------------------------
-- Bisimilarity of NWF Trees --
-------------------------------

-- Pointwise lifting of relations to trees
record ∞Pointwise {X : Set} (R : X → X → Set) (s t : NWFTree X) : Set
data Pointwise {X : Set} (R : X → X → Set) : (s t : NWFTree X) → Set

record ∞Pointwise R s t where
  coinductive
  field force : Pointwise R s t
open ∞Pointwise public

data Pointwise R where
  leaf : ∀ {x y} → R x y → Pointwise R (leaf x) (leaf y)
  node1 : ∀ {op op' x y s t} → R x y → ∞Pointwise R (force s) (force t) → Pointwise R (node1 op x s) (node1 op' y t)
  node2 : ∀ {op op' x y sl sr tl tr} → R x y → ∞Pointwise R (force sl) (force tl) → ∞Pointwise R (force sr) (force tr) → Pointwise R (node2 op x sl sr) (node2 op' y tl tr)
  nodeη : ∀ {op op' x y s t} → R x y → ∞Pointwise R (force s) (force t) → Pointwise R (nodeη op x s) (nodeη op' y t)


-- Bisim is pointwise ≡
_~_ : ∀ {X} → ∞NWFTree X → ∞NWFTree X → Set
s ~ t = ∞Pointwise _≡_ (force s) (force t)

-- Bisimilarity Extensionality.
-- True in OTT and HoTT(?), but not plain MLTT.
-- We may at some point need to postulate this.
BisimExt : (X : Set) → Set
BisimExt X = ∀ {s t : ∞NWFTree X} → s ~ t → s ≡ t

-----------------------------------
-- Paths in the Closure NWF Tree --
-----------------------------------

-- I'm expecting bisimiarity to be a pain to directly prove, and hoping that decomposing the tree
-- into its set of paths may make life easier. It probably won't, but who knows.

-- Paths through these infinite trees are co-lists.
record ∞Path {X : Set} (t : NWFTree X) : Set
data Path {X : Set} : NWFTree X → Set

record ∞Path t where
  coinductive
  field
    force : Path t
open ∞Path

data Path {X} where
  [] : ∀ {x} → Path (leaf x)
  down  : (op : Op₁) (x : X) {t : ∞NWFTree X}   → ∞Path (force t) → Path (node1 op x t)
  left  : (op : Op₂) (x : X) {l r : ∞NWFTree X} → ∞Path (force l) → Path (node2 op x l r)
  right : (op : Op₂) (x : X) {l r : ∞NWFTree X} → ∞Path (force r) → Path (node2 op x l r)
  under : (op : Opη) (x : X) {t : ∞NWFTree X}   → ∞Path (force t) → Path (nodeη op x t)
