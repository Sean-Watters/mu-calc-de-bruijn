{-# OPTIONS --safe --guardedness #-}
module Rational.Tree where

open import Data.Nat as N
open import Data.Fin hiding (_-_) renaming (_ℕ-ℕ_ to _-_)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality

open import MuCalc.Base using (Op₁; Op₂; Opη)
open import Codata.NWFTree as T hiding (Eventually; head; tree; _∈_; here)

-- Rational trees, presented as a syntax with binding in the style of Hamana.
-- Variables denote backedges.
data Tree (X : Set) (n : ℕ) : Set where
  loop : Fin n → Tree X n
  leaf : X → Tree X n
  node1 : Op₁ → X → Tree X n → Tree X n
  node2 : Op₂ → X → Tree X n → Tree X n → Tree X n
  nodeη : Opη → X → Tree X (suc n) → Tree X n

data NonVar {X : Set} {n : ℕ} : Tree X n → Set where
  instance leaf : ∀ {x} → NonVar (leaf x)
  instance node1 : ∀ {op x} → {t : Tree X n} → NonVar (node1 op x t)
  instance node2 : ∀ {op x} → {tl tr : Tree X n} → NonVar (node2 op x tl tr)
  instance nodeη : ∀ {op x} → {t : Tree X (suc n)} → NonVar (nodeη op x t)


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

----------------
-- Eventually --
----------------

-- This is clearly not prop-valued, because we can follow loops as often as we like. But that's good, as it
-- makes this definition line up 1:1 with Eventually for NWF trees.
data Eventually {X : Set} (P : X → Set) : ∀ {n} → (Γ : Scope X n) → Tree X n → Set where
  loop    : ∀ {n} {x : Fin n} {Γ : Scope X n} → Eventually P Γ (lookup Γ x) → Eventually P Γ (loop x)
  leaf    : ∀ {x n} {Γ : Scope X n} → P x → Eventually P Γ (leaf x)
  here1   : ∀ {op x n} {Γ : Scope X n} {t : Tree X n} → P x → Eventually P Γ (node1 op x t)
  there1  : ∀ {op x n} {Γ : Scope X n} {t : Tree X n} → Eventually P Γ t   → Eventually P Γ (node1 op x t)
  here2   : ∀ {op x n} {Γ : Scope X n} {l r : Tree X n} → P x → Eventually P Γ (node2 op x l r)
  there2l : ∀ {op x n} {Γ : Scope X n} {l r : Tree X n} → Eventually P Γ l → Eventually P Γ (node2 op x l r)
  there2r : ∀ {op x n} {Γ : Scope X n} {l r : Tree X n} → Eventually P Γ r → Eventually P Γ (node2 op x l r)
  hereη   : ∀ {op x n} {Γ : Scope X n} {t : Tree X (suc n)} → P x → Eventually P Γ (nodeη op x t)
  thereη  : ∀ {op x n} {Γ : Scope X n} {t : Tree X (suc n)} → Eventually P (nodeη op x t ,- Γ) t → Eventually P Γ (nodeη op x t)

_∈_ : {X : Set} → X → Tree X 0 → Set
x ∈ t = Eventually (_≡ x) [] t

----------------------------
-- Unfolding to NWF Trees --
----------------------------

head : ∀ {X n} → (Γ : Scope X n) → Tree X n → X
head Γ (leaf x) = x
head Γ (node1 op x t) = x
head Γ (node2 op x l r) = x
head Γ (nodeη op x t) = x
head (t ,- Γ) (loop zero) = head Γ t
head (t ,- Γ) (loop (suc x)) = head Γ (loop x)

unfold : ∀ {X n} → (Γ : Scope X n) → Tree X n → ∞NWFTree X
tree : ∀ {X n} → (Γ : Scope X n) → Tree X n → NWFTree X

tree Γ (leaf x) = leaf
tree Γ (node1 op x t) = node1 op (unfold Γ t)
tree Γ (node2 op x l r) = node2 op (unfold Γ l) (unfold Γ r)
tree Γ (nodeη op x t) = nodeη op (unfold (nodeη op x t ,- Γ) t)
tree (t ,- Γ) (loop zero) = tree Γ t
tree (t ,- Γ) (loop (suc x)) = tree Γ (loop x)

T.head (unfold Γ t) = head Γ t
T.tree (unfold Γ t) = tree Γ t

----------------
-- Operations --
----------------

size : ∀ {X n} → Tree X n → ℕ
size (loop x) = 0
size (leaf x) = 1
size (node1 _ _ t) = suc (size t)
size (node2 _ _ tl tr) = suc (size tl N.+ size tr)
size (nodeη _ _ t) = suc (size t)


---------------------------------
-- `here` for Any & Eventually --
---------------------------------

-- -- `here` for Any
-- here-any : ∀ {X n x} {P : X → Set} (Γ : Scope X n) (t : Tree X n)
--          → {{_ : NonVar t}}
--          → P x → x ≡ head Γ t → Any P t
-- here-any Γ (leaf x) px refl = leaf px
-- here-any Γ (node1 x x₁ t) px refl = here1 px
-- here-any Γ (node2 x x₁ t t₁) px refl = here2 px
-- here-any Γ (nodeη x x₁ t) px refl = hereη px

rescope-NonVar : ∀ {X n m} (ρ : Fin n → Fin m) (t : Tree X n) → NonVar t → NonVar (rescope ρ t)
rescope-NonVar ρ (leaf x₁) x = leaf
rescope-NonVar ρ (node1 x₁ x₂ t) x = node1
rescope-NonVar ρ (node2 x₁ x₂ t t₁) x = node2
rescope-NonVar ρ (nodeη x₁ x₂ t) x = nodeη

lookup-NonVar : ∀ {X n} → (Γ : Scope X n) → (x : Fin n) → NonVar (lookup Γ x)
lookup-NonVar (_,-_ t {{p}} Γ) zero = rescope-NonVar suc t p
lookup-NonVar (t ,- Γ) (suc x) = rescope-NonVar suc (lookup Γ x) (lookup-NonVar Γ x)

head-rescope : ∀ {X n} → (Γ : Scope X n) (t : Tree X n) {{_ : NonVar t}} → head Γ t ≡ head (t ,- Γ) (rescope suc t)
head-rescope Γ (leaf x) = refl
head-rescope Γ (node1 x x₁ t) = refl
head-rescope Γ (node2 x x₁ t t₁) = refl
head-rescope Γ (nodeη x x₁ t) = refl


head-rescope-suc : ∀ {X n} (a b : Tree X n) {{_ : NonVar a}} {{_ : NonVar b}} (Γ : Scope X n) (t : Tree X n) → head (a ,- Γ) (rescope suc t) ≡ head (b ,- Γ) (rescope suc t)
head-rescope-suc a b Γ (loop x) = refl
head-rescope-suc a b Γ (leaf x) = refl
head-rescope-suc a b Γ (node1 x x₁ t) = refl
head-rescope-suc a b Γ (node2 x x₁ t t₁) = refl
head-rescope-suc a b Γ (nodeη x x₁ t) = refl

head-loop : ∀ {X n} → (Γ : Scope X n) (x : Fin n) → head Γ (loop x) ≡  head Γ (lookup Γ x)
head-loop (t ,- Γ) zero = head-rescope Γ t
head-loop (t ,- Γ) (suc x) =
  begin
    head (t ,- Γ) (loop (suc x))
  ≡⟨ head-loop Γ x ⟩
    head Γ (lookup Γ x)
  ≡⟨ head-rescope Γ (lookup Γ x) {{lookup-NonVar Γ x}}  ⟩
    head _ (rescope suc (lookup Γ x))
  ≡⟨ head-rescope-suc (lookup Γ x) t {{lookup-NonVar Γ x}} Γ (lookup Γ x) ⟩
    head (t ,- Γ) (lookup (t ,- Γ) (suc x))
  ∎ where open ≡-Reasoning


-- `here` for Eventually
here-NonVar : ∀ {X n x} {P : X → Set} (Γ : Scope X n) (t : Tree X n) {{_ : NonVar t}}
     → P x → x ≡ head Γ t → Eventually P Γ t
here-NonVar Γ (leaf _) px refl = leaf px
here-NonVar Γ (node1 _ _ _) px refl = here1 px
here-NonVar Γ (node2 _ _ _ _) px refl = here2 px
here-NonVar Γ (nodeη _ _ _) px refl = hereη px

here : ∀ {X n x} {P : X → Set} (Γ : Scope X n) (t : Tree X n)
     → P x → x ≡ head Γ t → Eventually P Γ t
here Γ (loop x) px refl = loop (here-NonVar Γ (lookup Γ x) {{lookup-NonVar Γ x}} px (head-loop Γ x))
here Γ (leaf x) px refl = leaf px
here Γ (node1 x x₁ t) px refl = here1 px
here Γ (node2 x x₁ t t₁) px refl = here2 px
here Γ (nodeη x x₁ t) px refl = hereη px
