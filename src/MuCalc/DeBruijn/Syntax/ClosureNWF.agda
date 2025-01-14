{-# OPTIONS --guardedness #-}
module MuCalc.DeBruijn.Syntax.ClosureNWF where

open import Data.Bool using (Bool; true; false)
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties
open import Data.Fin as F using (Fin) renaming (_ℕ-ℕ_ to _-_)
open import Data.Product
open import Data.Sum

open import Function using (_$_)

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.Isomorphism
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star

open import MuCalc.DeBruijn.Base
open import MuCalc.DeBruijn.ExpansionMap

open import Rational.Tree as R hiding (Scope; ext; rescope; lookup; unwind; unfold)
open import Codata.NWFTree


----------------
-- Tree Stuff --
----------------

-- Coherence between formulas and rational trees
data Coh {At X : Set} : ∀ {n} → μML At n → R.Tree X n → Set where
  var : ∀ {n x} → Coh {n = n} (var x) (loop x)
  leaf : ∀ {op x n} → Coh {n = n} (μML₀ op) (leaf x) -- all leaves are coherent? maybe that's right? it kindof makes sense...
  node1 : ∀ {op x n} {ϕ : μML At n} {t : R.Tree X n} → Coh ϕ t → Coh (μML₁ op ϕ) (node1 op x t)
  node2 : ∀ {op x n} {ϕ ψ : μML At n} {l r : R.Tree X n} → Coh ϕ l → Coh ψ r → Coh (μML₂ op ϕ ψ) (node2 op x l r)
  nodeη : ∀ {op x n} {ϕ : μML At (suc n)} {t : R.Tree X (suc n)} → Coh ϕ t → Coh (μMLη op ϕ) (nodeη op x t)

-- Coherence between scopes of formulas and scopes of rational trees.
data ScCoh {At : Set} : ∀ {n} → Scope At n → R.Scope (μML At 0) n → Set where
  [] : ScCoh [] []
  _-,_ : ∀ {n} {Γ : Scope At n} {Γ₀ : μML At n} {{_ : IsFP Γ₀}} {Δ : R.Scope (μML At 0) n} {Δ₀ : R.Tree (μML At 0) n}
       → ScCoh Γ Δ → Coh Γ₀ Δ₀ → ScCoh (Γ₀ ,- Γ) (Δ₀ ,- Δ)

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

closure : ∀ {At} (ϕ : μML At 0) → ∞NWFTree (μML At 0)
force (closure ξ@(μML₀ op)) = leaf ξ
force (closure ξ@(μML₁ op ϕ)) = node1 op ξ (closure ϕ)
force (closure ξ@(μML₂ op ϕl ϕr)) = node2 op ξ (closure ϕl) (closure ϕr)
force (closure ξ@(μMLη op ϕ)) = nodeη op ξ (closure (unfold ξ))


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
closure-complete (μMLη op ξ) (thru .(μMLη op ξ) {{fp}} ◅ pxs) = thereη (closure-complete _ pxs )

-------------------------------
-- Finiteness of the Closure --
-------------------------------

---------
-- Plan:
-- (1) Define an inductive presentation of rational trees, and their unfoldings to nwf trees.
-- (2) Define the closure algoritm as a rational tree, via the expansion map.
-- (3) Define bisimilarity for nwf trees.
-- (4) Prove bisimilarity between the coinductive algorithm and the unfolding of the inductive algorithm.
---------

----------------------------------------------------
-- The Rational-by-Construction Closure Algorithm --
----------------------------------------------------

rational-closure : ∀ {At n} (Γ : Scope At n) (ϕ : μML At n) → R.Tree (μML At 0) n
rational-closure Γ ξ@(var x) = loop x
rational-closure Γ ξ@(μML₀ op) = leaf (expand Γ ξ)
rational-closure Γ ξ@(μML₁ op ϕ) = node1 op (expand Γ ξ) (rational-closure Γ ϕ)
rational-closure Γ ξ@(μML₂ op ϕl ϕr) = node2 op (expand Γ ξ) (rational-closure Γ ϕl) (rational-closure Γ ϕr)
rational-closure Γ ξ@(μMLη op ϕ) = nodeη op (expand Γ ξ) (rational-closure (ξ ,- Γ) ϕ)


-- Properties --



-- The rational tree produced has the same shape as the formula
rational-closure-coh : ∀ {At n} {Γ : Scope At n} (ϕ : μML At n) → Coh ϕ (rational-closure Γ ϕ)
rational-closure-coh (var x) = var
rational-closure-coh (μML₀ op) = leaf
rational-closure-coh (μML₁ op ϕ) = node1 (rational-closure-coh ϕ)
rational-closure-coh (μML₂ op ϕl ϕr) = node2 (rational-closure-coh ϕl) (rational-closure-coh ϕr)
rational-closure-coh (μMLη op ϕ) = nodeη (rational-closure-coh ϕ)


-- We can't get away with only considering empty contexts, because we do need to traverse binders.
-- But the coinductive closure algorithm is only defined on sentences, so we cant plug arbitrary subformulas in there.
-- Lets try with the expansion map...it may even work...
rational-closure-unfolding-bisim : ∀ {At n} {Γ : Scope At n} {Δ : R.Scope (μML At 0) n}
                                  → ScCoh Γ Δ → (ξ : μML At n) → closure (expand Γ ξ) ~ R.unfold Δ (rational-closure Γ ξ)
force (rational-closure-unfolding-bisim Γ (μML₀ op)) = leaf refl
force (rational-closure-unfolding-bisim Γ (μML₁ op ϕ)) = node1 refl (rational-closure-unfolding-bisim Γ ϕ)
force (rational-closure-unfolding-bisim Γ (μML₂ op ϕl ϕr)) = node2 refl (rational-closure-unfolding-bisim Γ ϕl) (rational-closure-unfolding-bisim Γ ϕr)
force (rational-closure-unfolding-bisim {At} {n} {Γ} {Δ} p (μMLη op ϕ)) = nodeη refl {!rational-closure-unfolding-bisim!}
force (rational-closure-unfolding-bisim Γ (var x)) = {!x!}

-- If the context is empty, then the expansion map is the identity, so we get the statement we wanted all along.
rational-closure-unfolding-bisim-sentence : ∀ {At} (ξ : μML At 0) → closure ξ ~ R.unfold R.[] (rational-closure [] ξ)
rational-closure-unfolding-bisim-sentence ξ = {!rational-closure-unfolding-bisim [] ξ!} -- rational-closure-unfolding-bisim [] ξ


-- The set of formulas in the closure is finite. todo: might want a different notion of finiteness.
-- Hopefully this should follow via some reasoning about the above.
closure-finite : ∀ {At} (ξ : μML At 0) → Σ[ n ∈ ℕ ] Closure ξ ≃ Fin n
closure-finite ξ = {!!}

