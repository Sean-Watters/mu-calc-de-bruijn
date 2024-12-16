{-# OPTIONS --guardedness #-}
module MuCalc.DeBruijn.Syntax.ClosureNWF where

-- open import Algebra.Structures.Propositional
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties using (m≤n⇒m≤1+n; ≤-refl)
open import Data.Fin as F using (Fin; fromℕ; fold; toℕ; _ℕ-_)
open import Data.Fin.Properties using (_≟_)
open import Data.Product
-- open import Data.Tree.Backedges
open import Data.Vec.Snoc
open import Data.Empty using () renaming (⊥ to Zero)
open import Function using (_∘_; flip)
open import MuCalc.DeBruijn.Base
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.Isomorphism
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
open import Relation.Nullary
open import Data.Unit renaming (⊤ to 𝟙)

-------------
--  Scopes --
-------------

-- Vectors of fixpoint formulas, with the extra trick that the number of
-- free variables allowed depends on its position in the vector
data Scope (At : Set) : ℕ → Set where
  [] : Scope At zero
  _-,_ : ∀ {n} → (Γ₀ : Scope At n) → (ϕ : μML At n) → {{_ : IsFP ϕ}} → Scope At (suc n)

lookup : ∀ {At n} → (Γ : Scope At n) → (x : Fin n) → μML At n
lookup (Γ -, ϕ) F.zero = rescope F.suc ϕ
lookup (Γ -, ϕ) (F.suc x) = rescope F.suc (lookup Γ x)

-------------------------------
-- Definition of the Closure --
-------------------------------

-- The one-step closure relation.
-- This is the foundation of the correctness criteria for the algorithm.
data _~C~>_ {At : Set} : (ϕ ψ : μML At 0) → Set where
  down  : ∀ op ϕ → μML₁ op ϕ ~C~> ϕ
  left  : ∀ op ϕ ψ → μML₂ op ϕ ψ ~C~> ϕ
  right : ∀ op ϕ ψ → μML₂ op ϕ ψ ~C~> ψ
  thru  : ∀ ϕ → {{_ : IsFP ϕ}} → ϕ ~C~> unfold ϕ

-- ϕ is in the closure of ξ if there is a path ξ ~...~> ϕ.
-- That is, the membership relation for the Fischer-Ladner closure set is the transitive reflexive
-- closure of _<~C~_
_∈-Closure_ : {At : Set} → (ϕ ξ : μML At 0) → Set
ϕ ∈-Closure ξ = Star (_~C~>_) ξ ϕ

-- The closure of ϕ is defined as the set of all formulas reachable in this way from ϕ.
Closure : {At : Set} → μML At 0 → Set
Closure {At} ϕ = Σ[ ψ ∈ μML At 0 ] (ψ ∈-Closure ϕ)

---------------------------
-- Computing the Closure --
---------------------------

-- A type of nonwellfounded trees with nodes labelled
-- by ■/◆/∧/∨/μ/μ, storing data at both leaves and nodes

record ∞NWFTree (X : Set) : Set
data NWFTree (X : Set) : Set

record ∞NWFTree X where
  coinductive
  field
    force : NWFTree X
open ∞NWFTree

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

closure : ∀ {At} (ϕ : μML At 0) → ∞NWFTree (μML At 0)
force (closure ξ@(μML₀ op)) = leaf ξ
force (closure ξ@(μML₁ op ϕ)) = node1 op ξ (closure ϕ)
force (closure ξ@(μML₂ op ϕl ϕr)) = node2 op ξ (closure ϕl) (closure ϕr)
force (closure ξ@(μMLη op ϕ)) = nodeη op ξ (closure (unfold ξ))

-----------------------------
-- Properties of Unfolding --
-----------------------------

-- unfold-leaf : ∀ {op} → unfold (μML₀ op) ≡ μML₀ op
-- unfold-leaf = ?

------------------------------------------
-- Correctness of the Closure Algorithm --
------------------------------------------

-- Everything reachable via the closure algorithm is in the
-- closure relation.
closure-sound : ∀ {At} (ξ : μML At 0) {ϕ : μML At 0}
                → (ϕ ∈T closure ξ) → (ϕ ∈-Closure ξ)
closure-sound (μML₀ op) (herel refl) = ε
closure-sound (μML₁ op ξ) (here1 refl) = ε
closure-sound (μML₁ op ξ) (there1 p) = down op ξ ◅ (closure-sound ξ p)
closure-sound (μML₂ op ξl ξr) (here2 refl) = ε
closure-sound (μML₂ op ξl ξr) (there2l p) = left  op ξl ξr ◅ (closure-sound ξl p)
closure-sound (μML₂ op ξl ξr) (there2r p) = right op ξl ξr ◅ (closure-sound ξr p)
closure-sound (μMLη op ξ) (hereη refl) = ε
closure-sound (μMLη op ξ) (thereη p) = thru (μMLη op ξ) ◅ (closure-sound (unfold (μMLη op ξ)) p)


-- And the other direction.
-- Every formula in the closure is reached by the algorithm.
closure-complete : ∀ {At} (ξ : μML At 0) {ϕ : μML At 0}
                 → (ϕ ∈-Closure ξ) → (ϕ ∈T closure ξ)
closure-complete (μML₀ op) ε = herel refl
closure-complete (μML₀ op) (thru .(μML₀ op) {{()}} ◅ pxs) -- leaves are leaves; the `there` case is impossible
closure-complete (μML₁ op ξ) ε = here1 refl
closure-complete (μML₁ op ξ) (down .op .ξ ◅ pxs) = there1 (closure-complete ξ pxs)
closure-complete (μML₂ op ξ ξ₁) ε = here2 refl
closure-complete (μML₂ op ξl ξr) (left .op .ξl .ξr ◅ pxs) = there2l (closure-complete ξl pxs)
closure-complete (μML₂ op ξl ξr) (right .op .ξl .ξr ◅ pxs) = there2r (closure-complete ξr pxs)
closure-complete (μMLη op ξ) ε = hereη refl
closure-complete (μMLη op ξ) (thru .(μMLη op ξ) ◅ pxs) = thereη (closure-complete _ pxs)



-- The set of formulas in the closure is finite.
-- TODO: This is a bad notion of finiteness, it will make proofs way harder than needed.
-- Counting....ugh. Why use arithmetic when we can use structure! Return of the syntax with binding.
closure-finite : ∀ {At} (ξ : μML At 0) → Σ[ n ∈ ℕ ] Closure ξ ≃ Fin n
closure-finite = {!!}

-----------------------------------
-- Paths in the Closure NWF Tree --
-----------------------------------

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
