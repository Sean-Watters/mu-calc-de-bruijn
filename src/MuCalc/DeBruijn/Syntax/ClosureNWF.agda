{-# OPTIONS --guardedness #-}
module MuCalc.DeBruijn.Syntax.ClosureNWF where

open import Data.Nat hiding (_≟_)
open import Data.Fin as F using (Fin)
open import Data.Product

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.Isomorphism
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star

open import MuCalc.DeBruijn.Base
open import Rational.Tree as R hiding (Scope; ext; rescope; lookup; unfold)
open import Codata.NWFTree

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
closure-complete (μMLη op ξ) (thru .(μMLη op ξ) ◅ pxs) = thereη (closure-complete _ pxs)

-------------------------------
-- Finiteness of the Closure --
-------------------------------

-- Sketch:
-- (1) (DONE!) Define an inductive presentation of rational trees, and their unfoldings to nwf trees.
-- (2) Define the closure algoritm as a rational tree, via the expansion map.
-- (3) (DONE!) Define bisimilarity for nwf trees.
-- (4) Prove bisimilarity between the coinductive algorithm and the unfolding of the inductive algorithm.

-- The expansion map
expand : ∀ {n At} → Scope At n → μML At n → μML At 0
expand [] ϕ = ϕ
expand (Γ -, Γ₀) ϕ = expand Γ (ϕ [ Γ₀ ])

rational-closure : ∀ {At n} (Γ : Scope At n) (ϕ : μML At n) → R.Tree (μML At 0) n
rational-closure Γ ξ@(var x) = loop x
rational-closure Γ ξ@(μML₀ op) = leaf (expand Γ ξ)
rational-closure Γ ξ@(μML₁ op ϕ) = node1 op (expand Γ ξ) (rational-closure Γ ϕ)
rational-closure Γ ξ@(μML₂ op ϕl ϕr) = node2 op (expand Γ ξ) (rational-closure Γ ϕl) (rational-closure Γ ϕr)
rational-closure Γ ξ@(μMLη op ϕ) = nodeη op (expand Γ ξ) (rational-closure (Γ -, ξ) ϕ)

-- OK, now time to think.
-- We can't get away with only doing empty contexts, because we do need to traverse binders.
-- But the coinductive closure algorithm is only defined on sentences.
{-
rational-closure-unfolding-bisim : ∀ {At} (ξ : μML At 0) → closure ξ ~ R.unfold R.[] (rational-closure [] ξ)
force (rational-closure-unfolding-bisim (μML₀ op)) = leaf refl
force (rational-closure-unfolding-bisim (μML₁ op ϕ)) = node1 refl (rational-closure-unfolding-bisim ϕ)
force (rational-closure-unfolding-bisim (μML₂ op ϕl ϕr)) = node2 refl (rational-closure-unfolding-bisim ϕl) (rational-closure-unfolding-bisim ϕr)
force (rational-closure-unfolding-bisim (μMLη op ϕ)) = nodeη refl {!lemma !}
-}

-- Let's try for a bisim on the closure of the *expansion*
-- Is this even true?
-- Do we need some kind of coherence between Γ and Δ?
rational-closure-unfolding-bisim : ∀ {At n} (Γ : Scope At n) (Δ : R.Scope (μML At 0) n) (ξ : μML At n) → closure (expand Γ ξ) ~ R.unfold Δ (rational-closure Γ ξ)
force (rational-closure-unfolding-bisim Γ Δ ξ) = {!ξ!}


-- The set of formulas in the closure is finite. todo: might want a different notion of finiteness
closure-finite : ∀ {At} (ξ : μML At 0) → Σ[ n ∈ ℕ ] Closure ξ ≃ Fin n
closure-finite ξ = {!!}
