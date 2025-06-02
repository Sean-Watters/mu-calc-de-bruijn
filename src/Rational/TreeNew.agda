{-# OPTIONS --safe --guardedness #-}
module Rational.TreeNew where

open import Data.Nat as N
open import Data.Fin hiding (_-_) renaming (_ℕ-ℕ_ to _-_)
open import Data.Fin.Renaming using (Rename; ext)
open import Data.Product
open import Data.Thinning as Th hiding (id)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality

open import MuCalc.Base using (Op₁; Op₂; Opη)
open import Codata.NWFTree as T hiding (Any; Any-step; head; tree; _∈_; here)


mutual
-- Our rational trees store X's at both nodes and leaves, and include encodings of backedges
-- in the form of variables.
  data Tree (X : Set) (n : ℕ) : Set where
    step : (x : X) → (t : Tree-step X n) → Tree X n -- either we store an element then take a step,
    var : (x : Fin n) → Tree X n             -- or we follow a backedge and loop back up the tree.

  data Tree-step (X : Set) (n : ℕ) : Set where
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


-- Rescoping
mutual
  rename : ∀ {X n m} → Rename n m -- if we have an mapping of i vars to j vars...
          → Tree X n → Tree X m -- then we can rename i-terms to be j-terms.
  rename ρ (step x t) = step x (rename-step ρ t)
  rename ρ (var x) = var (ρ x)

  rename-step : ∀ {X n m} → Rename n m
               → Tree-step X n → Tree-step X m
  rename-step ρ leaf = leaf
  rename-step ρ (node1 op t) = node1 op (rename ρ t)
  rename-step ρ (node2 op tl tr) = node2 op (rename ρ tl) (rename ρ tr)
  rename-step ρ (nodeη op t) = nodeη op (rename (ext ρ) t)

lookup : ∀ {X n} → (Γ : Scope X n) → (x : Fin n) → Tree X n
lookup (t ,- Γ) zero = rename suc t
lookup (t ,- Γ) (suc x) = rename suc (lookup Γ x)

rename-NonVar : ∀ {X n m} {t : Tree X n} {ρ : Rename n m} → {{nv : NonVar t}} → NonVar (rename ρ t)
rename-NonVar {{nv = step}} = step

_++_ : ∀ {X a b} → Scope X a → Scope X b → Scope X (a N.+ b)
[] ++ Δ = Δ
(t ,- Γ) ++ Δ = _,-_ (rename (embed (plusR _)) t) {{rename-NonVar}} (Γ ++ Δ)

mutual
  -- A data type witnessing that renaming `tx` by `ρ` yields `ty`.
  data IsRenaming {X : Set} {n m : ℕ} (ρ : Rename n m) : (tx : Tree X n) (ty : Tree X m) → Set where
    step : ∀ {x y} {tx : Tree-step X n} {ty : Tree-step X m} → x ≡ y → IsRenaming-step ρ tx ty → IsRenaming ρ (step x tx) (step y ty)
    var : ∀ {x y} → ρ x ≡ y → IsRenaming ρ (var x) (var y)

  data IsRenaming-step {X : Set} : {n m : ℕ} (ρ : Rename n m) (tx : Tree-step X n) (ty : Tree-step X m) → Set where
    leaf : ∀ {n m} {ρ : Rename n m} → IsRenaming-step ρ leaf leaf
    node1 : ∀ {n m} {ρ : Rename n m} op → {tx : Tree X n} {ty : Tree X m}
          → IsRenaming ρ tx ty → IsRenaming-step ρ (node1 op tx) (node1 op ty)
    node2 : ∀ {n m} {ρ : Rename n m} op → {txl txr : Tree X n} {tyl tyr : Tree X m}
          → IsRenaming ρ txl tyl → IsRenaming ρ txr tyr → IsRenaming-step ρ (node2 op txl txr) (node2 op tyl tyr)
    nodeη : ∀ {n m} {ρ : Rename n m} op → {tx : Tree X (suc n)} {ty : Tree X (suc m)}
          → IsRenaming (ext ρ) tx ty → IsRenaming-step ρ (nodeη op tx) (nodeη op ty)

---------------
-- Thinnings --
---------------

-- Thinnings of scopes. More abstraction would have been nice, but oh well.
-- We define this mutually with the function that converts such a thinning to a renaming.
data _⊑_ {X : Set} : {n m : ℕ} → Scope X n → Scope X m → Set
erase : ∀ {X n m} {Γ : Scope X n} {Δ : Scope X m} → Γ ⊑ Δ → Thin n m
embed' : ∀ {X n m} {Γ : Scope X n} {Δ : Scope X m} → Γ ⊑ Δ → Rename n m

data _⊑_ {X} where
  end : [] ⊑ []
  inj : ∀ {n m} {s : Tree X n} {t : Tree X m} {{nvs : NonVar s}} {{nvt : NonVar t}}
      → {Γ : Scope X n} {Δ : Scope X m}
      → (θ : Γ ⊑ Δ)
      → IsRenaming (embed' θ) s t
      → (s ,- Γ) ⊑ (t ,- Δ)
  pad : ∀ {n m} {t : Tree X m} {{nvt : NonVar t}} {Γ : Scope X n} {Δ : Scope X m} → Γ ⊑ Δ → Γ ⊑ (t ,- Δ)

erase end = end
erase (inj r θ) = inj (erase r)
erase (pad θ) = pad (erase θ)

embed' (inj θ eq) zero = zero
embed' (inj θ eq) (suc x) = suc (embed' θ x)
embed' (pad θ) x = suc (embed' θ x)

--------------------------
-- Equivalence of Trees --
--------------------------

-- Two trees are equivalent if there's a thinning between their scopes that sends the variables to the right
-- places.
[_⊢_]≈[_⊢_] : {X : Set} {n m : ℕ} (Γ : Scope X n) → (tx : Tree X n) → (Δ : Scope X m) → (ty : Tree X m) → Set
[ Γ ⊢ tx ]≈[ Δ ⊢ ty ] = Σ[ θ ∈ Γ ⊑ Δ ] (IsRenaming (embed' θ) tx ty)

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


