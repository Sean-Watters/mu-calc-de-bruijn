{-# OPTIONS --safe --guardedness #-}
module Rational.TreeNew where

open import Data.Nat as N
open import Data.Fin hiding (_-_) renaming (_ℕ-ℕ_ to _-_)
open import Data.Thinning as Th hiding (id)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality

open import MuCalc.Base using (Op₁; Op₂; Opη)
open import Codata.NWFTree as T hiding (Any; Any-step; head; tree; _∈_; here)


-- Our rational trees store X's at both nodes and leaves, and include encodings of backedges
-- in the form of variables.
data Tree (X : Set) (n : ℕ) : Set
data Tree-step (X : Set) (n : ℕ) : Set

data Tree X n where
  step : (x : X) → (t : Tree-step X n) → Tree X n -- either we store an element then take a step,
  var : (x : Fin n) → Tree X n             -- or we follow a backedge and loop back up the tree.

data Tree-step X n where
  leaf : Tree-step X n
  node1 : (op : Op₁) → (t : Tree X n) → Tree-step X n
  node2 : (op : Op₂) → (tl : Tree X n) → (tr : Tree X n) → Tree-step X n
  nodeη : (op : Opη) → (t : Tree X (suc n)) → Tree-step X n -- μ/ν nodes are the variable binders


-- A useful predicate on trees
data NonVar {X : Set} {n : ℕ} : Tree X n → Set where
  instance step : ∀ {x t} → NonVar (step x t)

------------
-- Scopes --
------------

-- Scopes for RTrees
-- This is *begging* for abstraction, look how similar it was to the scopes for formulas!
data Scope (X : Set) : ℕ → Set where
  [] : Scope X zero
  _,-_ : ∀ {n} → (t : Tree X n) → {{_ : NonVar t}} → (Γ₀ : Scope X n) → Scope X (suc n)

-- Scope extension
ext : ∀ {n m} → (Fin n → Fin m)
    → Fin (suc n) → Fin (suc m)
ext ρ zero = zero
ext ρ (suc x) = suc (ρ x)

-- Rescoping
mutual
  rename : ∀ {X n m} → (Fin n → Fin m) -- if we have an mapping of i vars to j vars...
          → Tree X n → Tree X m -- then we can rename i-terms to be j-terms.
  rename ρ (step x t) = step x (rename-step ρ t)
  rename ρ (var x) = var (ρ x)

  rename-step : ∀ {X n m} → (Fin n → Fin m)
               → Tree-step X n → Tree-step X m
  rename-step ρ leaf = leaf
  rename-step ρ (node1 op t) = node1 op (rename ρ t)
  rename-step ρ (node2 op tl tr) = node2 op (rename ρ tl) (rename ρ tr)
  rename-step ρ (nodeη op t) = nodeη op (rename (ext ρ) t)

lookup : ∀ {X n} → (Γ : Scope X n) → (x : Fin n) → Tree X n
lookup (t ,- Γ) zero = rename suc t
lookup (t ,- Γ) (suc x) = rename suc (lookup Γ x)

rename-NonVar : ∀ {X n m} {t : Tree X n} {ρ : Fin n → Fin m} → {{nv : NonVar t}} → NonVar (rename ρ t)
rename-NonVar {{nv = step}} = step

_++_ : ∀ {X a b} → Scope X a → Scope X b → Scope X (a N.+ b)
[] ++ Δ = Δ
(t ,- Γ) ++ Δ = _,-_ (rename (embed (plusR _)) t) {{rename-NonVar}} (Γ ++ Δ)

---------------
-- Thinnings --
---------------

-- Thinnings of scopes. More abstraction would have been nice, but oh well.
-- We define this mutually with the function that converts such a thinning to a renaming.
data _⊑_ {X : Set} : {n m : ℕ} → Scope X n → Scope X m → Set
embed' : ∀ {X n m} {Γ : Scope X n} {Δ : Scope X m} → Γ ⊑ Δ → (Fin n → Fin m)

data _⊑_ {X} where
  end : [] ⊑ []
  inj : ∀ {n m} {s : Tree X n} {t : Tree X m} {{_ : NonVar s}} {{_ : NonVar t}}
      → {Γ : Scope X n} {Δ : Scope X m}
      → (θ : Γ ⊑ Δ)
      → rename (embed' θ) s ≡ t
      → (s ,- Γ) ⊑ (t ,- Δ)
  pad : ∀ {n m} {t : Tree X m} {{_ : NonVar t}} {Γ : Scope X n} {Δ : Scope X m} → Γ ⊑ Δ → Γ ⊑ (t ,- Δ)

embed' (inj θ eq) zero = zero
embed' (inj θ eq) (suc x) = suc (embed' θ x)
embed' (pad θ) x = suc (embed' θ x)

---------
-- Any --
---------

-- The `Any` predicate transformer; paths through the tree to an element satisfying
-- a predicate P. This is a little different from the usual `Any` because we can follow
-- backedges as much as we like, but that's a good thing as it makes this definition line
-- up 1:1 with `Any` for NWF trees.
data Any {X : Set} (P : X → Set) : ∀ {n} → (Γ : Scope X n) → Tree X n → Set
data Any-step {X : Set} (P : X → Set) (x : X) : ∀ {n} → (Γ : Scope X n) → Tree-step X n → Set

data Any {X} P where
  here : ∀ {n x} {Γ : Scope X n} {t : Tree-step X n} → P x → Any P Γ (step x t)
  step : ∀ {n x} {Γ : Scope X n} {t : Tree-step X n} → Any-step P x Γ t → Any P Γ (step x t)
  loop : ∀ {n x} {Γ : Scope X n} → Any P Γ (lookup Γ x) → Any P Γ (var x)

data Any-step {X} P x where -- needs to know the last x that was stored so that the scope can be correct in the last step
  leaf   : ∀ {n} {Γ : Scope X n} → Any-step P x Γ leaf
  node1  : ∀ {op n} {Γ : Scope X n} {t : Tree X n} → Any P Γ t → Any-step P x Γ (node1 op t)
  node2l : ∀ {op n} {Γ : Scope X n} {tl : Tree X n} {tr : Tree X n} → Any P Γ tl → Any-step P x Γ (node2 op tl tr)
  node2r : ∀ {op n} {Γ : Scope X n} {tl : Tree X n} {tr : Tree X n} → Any P Γ tr → Any-step P x Γ (node2 op tl tr)
  nodeη  : ∀ {op n} {Γ : Scope X n} {t : Tree X (suc n)} → Any P (step x (nodeη op t) ,- Γ) t → Any-step P x Γ (nodeη op t)

_∈_ : {X : Set} → X → Tree X 0 → Set
x ∈ t = Any (_≡ x) [] t

----------------------------
-- Unfolding to NWF Trees --
----------------------------


head : ∀ {X n} → (Γ : Scope X n) → Tree X n → X
head Γ (step x t) = x
head (t ,- Γ) (var zero) = head Γ t -- scopes aren't allowed to store vars exactly so that this is possible
head (t ,- Γ) (var (suc x)) = head Γ (var x)

mutual
  unfold : ∀ {X n} → (Γ : Scope X n) → Tree X n → ∞NWFTree X
  unfold Γ t .T.head = head Γ t
  unfold Γ t .T.tree = unfold-subtree Γ t

  unfold-subtree : ∀ {X n} → (Γ : Scope X n) → Tree X n → NWFTree X
  unfold-subtree Γ (step x leaf) = leaf
  unfold-subtree Γ (step x (node1 op t)) = node1 op (unfold Γ t)
  unfold-subtree Γ (step x (node2 op tl tr)) = node2 op (unfold Γ tl) (unfold Γ tr)
  unfold-subtree Γ (step x (nodeη op t)) = nodeη op (unfold ((step x (nodeη op t)) ,- Γ) t)
  unfold-subtree (t ,- Γ) (var zero) = unfold-subtree Γ t
  unfold-subtree (t ,- Γ) (var (suc x)) = unfold-subtree Γ (var x)

----------------
-- Operations --
----------------

size : ∀ {X n} → Tree X n → ℕ
size (step x leaf) = 1
size (step x (node1 op t)) = suc (size t)
size (step x (node2 op tl tr)) = suc (size tl N.+ size tr)
size (step x (nodeη op t)) = suc (size t)
size (var x) = 0


