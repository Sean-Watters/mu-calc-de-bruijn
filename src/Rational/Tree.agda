{-# OPTIONS --guardedness #-}
module Rational.Tree where

open import Data.Nat
open import Data.Fin hiding (_-_) renaming (_ℕ-ℕ_ to _-_)
open import Function using (_$_)

open import MuCalc.DeBruijn.Base using (Op₁; Op₂; Opη)
open import Codata.NWFTree as T hiding (Eventually)

-- Rational trees, presented as a syntax with binding in the style of Hamana.
-- Variables denote backedges.
data Tree (X : Set) (n : ℕ) : Set where
  loop : Fin n → Tree X n
  leaf : X → Tree X n
  node1 : Op₁ → X → Tree X n → Tree X n
  node2 : Op₂ → X → Tree X n → Tree X n → Tree X n
  nodeη : Opη → X → Tree X (suc n) → Tree X n

------------
-- Scopes --
------------

-- Scopes for RTrees
-- This is *begging* for abstraction, look how similar it was to the scopes for formulas!
data Scope (X : Set) : ℕ → Set where
  [] : Scope X zero
  _,-_ : ∀ {n} → (t : Tree X n) (Γ₀ : Scope X n) → Scope X (suc n)

-- Scope extension
ext : ∀ {n m} → (Fin n → Fin m)
    → Fin (suc n) → Fin (suc m)
ext ρ zero = zero
ext ρ (suc x) = suc (ρ x)

rescope : ∀ {X n m} → (Fin n → Fin m) -- if we have an mapping of i vars to j vars...
        → Tree X n → Tree X m -- then we can rescope i-terms to be j-terms.
rescope ρ (loop x) = loop (ρ x)
rescope ρ (leaf x) = leaf x
rescope ρ (node1 op x t) = node1 op x (rescope ρ t)
rescope ρ (node2 op x l r) = node2 op x (rescope ρ l) (rescope ρ r)
rescope ρ (nodeη op x t) = nodeη op x (rescope (ext ρ) t)

lookup : ∀ {X n} → (Γ : Scope X n) → (x : Fin n) → Tree X n
lookup (t ,- Γ) zero = rescope suc t
lookup (t ,- Γ) (suc x) = rescope suc (lookup Γ x)

-- A more precise/unthinned version of lookup
lookup' : ∀ {X n} → (Γ : Scope X n) → (x : Fin n) → Tree X (n - (suc x))
lookup' (t ,- Γ) zero = t
lookup' (t ,- Γ) (suc x) = lookup' Γ x

-- "Unwinding" a scope back to some variable x.
-- ie, popping off everything up to and including x,
-- so that we're left with x's scope.
-- Pairs very naturally with lookup'.
unwind : ∀ {X n} → (Γ : Scope X n) → (x : Fin n) → Scope X (n - (suc x))
unwind (ϕ ,- Γ) zero = Γ
unwind (ϕ ,- Γ) (suc x) = unwind Γ x

--------------------
-- Any/Eventually --
--------------------

-- *Inductive* flavoured Any that *doesn't follow backedges*.
-- This is *not* Eventually for RTrees.
data Any {X : Set} (P : X → Set) : ∀ {n} → Tree X n → Set where
  here1   : ∀ {op x n} {t : Tree X n}       → P x     → Any P (node1 op x t)
  there1  : ∀ {op x n} {t : Tree X n}       → Any P t → Any P (node1 op x t)
  here2   : ∀ {op x n} {l r : Tree X n}     → P x     → Any P (node2 op x l r)
  there2l : ∀ {op x n} {l r : Tree X n}     → Any P l → Any P (node2 op x l r)
  there2r : ∀ {op x n} {l r : Tree X n}     → Any P r → Any P (node2 op x l r)
  hereη   : ∀ {op x n} {t : Tree X (suc n)} → P x     → Any P (nodeη op x t)
  thereη  : ∀ {op x n} {t : Tree X (suc n)} → Any P t → Any P (nodeη op x t)

-- Eventually for RTrees. Either we find a path to it in the inductive structure,
-- or we find a path to a variable and then a path from the landing point (which
-- *doesn't* loop another variable -- ie, an Any).
data Eventually {X : Set} (P : X → Set) : ∀ {n} → (Γ : Scope X n) → Tree X n → Set where
  loop    : ∀ {n} {x : Fin n} {Γ : Scope X n}               → Any P (lookup Γ x) → Eventually P Γ (loop x)
  here1   : ∀ {op x n} {Γ : Scope X n} {t : Tree X n}       → P x                → Eventually P Γ (node1 op x t)
  there1  : ∀ {op x n} {Γ : Scope X n} {t : Tree X n}       → Eventually P Γ t   → Eventually P Γ (node1 op x t)
  here2   : ∀ {op x n} {Γ : Scope X n} {l r : Tree X n}     → P x                → Eventually P Γ (node2 op x l r)
  there2l : ∀ {op x n} {Γ : Scope X n} {l r : Tree X n}     → Eventually P Γ l   → Eventually P Γ (node2 op x l r)
  there2r : ∀ {op x n} {Γ : Scope X n} {l r : Tree X n}     → Eventually P Γ r   → Eventually P Γ (node2 op x l r)
  hereη   : ∀ {op x n} {Γ : Scope X n} {t : Tree X (suc n)} → P x                → Eventually P Γ (nodeη op x t)
  thereη  : ∀ {op x n} {Γ : Scope X n} {t : Tree X (suc n)} → Eventually P (nodeη op x t ,- Γ) t → Eventually P Γ (nodeη op x t)

----------------------------
-- Unfolding to NWF Trees --
----------------------------

-- termination check failed, unguarded :(
-- inlining lookup in a mutual doesn't help, either way we end up with an
-- unguarded corecursive call
-- Is there something like "productive coinduction" analogous to wellfounded induction?
-- Lets try and figure it out. In sketchpad/Coinduction/Productive
-- I really don't want to go back to the thing with the maybes, it seems too janky.
-- Would rather do it once and for all.

{-# TERMINATING #-} -- honest, 'guv. (will hopefully be able to drop in the PCoI stuff when it's ready, without too much overhead...)
unfold : ∀ {X n} → (Γ : Scope X n) → Tree X n → ∞NWFTree X
force (unfold Γ (loop x)) = force $ unfold (unwind Γ x) (lookup' Γ x)
force (unfold Γ (leaf x)) = leaf x
force (unfold Γ (node1 op x t)) = node1 op x (unfold Γ t)
force (unfold Γ (node2 op x l r)) = node2 op x (unfold Γ l) (unfold Γ r)
force (unfold Γ (nodeη op x t)) = nodeη op x (unfold (nodeη op x t ,- Γ) t)
