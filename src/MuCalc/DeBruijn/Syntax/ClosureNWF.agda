{-# OPTIONS --safe --guardedness #-}
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
open import Codata.NWFTree as T


----------------
-- Tree Stuff --
----------------

-- Coherence between formulas and rational trees
-- This may not be strong enough? Take a 2nd look with `expand-lookup-here` in mind
data Coh {At X : Set} : ∀ {n} → μML At n → R.Tree X n → Set where
  var : ∀ {n x} → Coh {n = n} (var x) (loop x)
  leaf : ∀ {op x n} → Coh {n = n} (μML₀ op) (leaf x) -- todo: it's almost certainly wrong that leaves don't have an op
  node1 : ∀ {op x n} {ϕ : μML At n} {t : R.Tree X n} → Coh ϕ t → Coh (μML₁ op ϕ) (node1 op x t)
  node2 : ∀ {op x n} {ϕ ψ : μML At n} {l r : R.Tree X n} → Coh ϕ l → Coh ψ r → Coh (μML₂ op ϕ ψ) (node2 op x l r)
  nodeη : ∀ {op x n} {ϕ : μML At (suc n)} {t : R.Tree X (suc n)} → Coh ϕ t → Coh (μMLη op ϕ) (nodeη op x t)

-- Coherence between scopes of formulas and scopes of rational trees.
data ScCoh {At : Set} : ∀ {n} → Scope At n → R.Scope (μML At 0) n → Set where
  [] : ScCoh [] []
  _,-_ : ∀ {n} {Γ : Scope At n} {Γ₀ : μML At n} {{_ : IsFP Γ₀}} {Δ : R.Scope (μML At 0) n} {Δ₀ : R.Tree (μML At 0) n}
       →  Coh Γ₀ Δ₀ → ScCoh Γ Δ → ScCoh (Γ₀ ,- Γ) (Δ₀ ,- Δ)

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
T.head (closure ξ) = ξ
T.tree (closure (μML₀ op)) = leaf
T.tree (closure (μML₁ op ϕ)) = node1 op (closure ϕ)
T.tree (closure (μML₂ op ϕl ϕr)) = node2 op (closure ϕl) (closure ϕr)
T.tree (closure (μMLη op ϕ)) = nodeη op (closure (unfold (μMLη op ϕ)))


------------------------------------------
-- Correctness of the Closure Algorithm --
------------------------------------------

-- Everything reachable via the closure algorithm is in the
-- closure relation.
closure-sound : ∀ {At} (ξ : μML At 0) {ϕ : μML At 0}
                → (ϕ ∈ closure ξ) → (ϕ ∈-Closure ξ)
closure-sound ξ (here refl) = ε
closure-sound (μML₁ op ξ) (there (node1 p)) = down op ξ ◅ (closure-sound ξ p)
closure-sound (μML₂ op ξl ξr) (there (node2l p)) = left  op ξl ξr ◅ (closure-sound ξl p)
closure-sound (μML₂ op ξl ξr) (there (node2r p)) = right op ξl ξr ◅ (closure-sound ξr p)
closure-sound (μMLη op ξ) (there (nodeη p)) = thru (μMLη op ξ) ◅ (closure-sound (unfold (μMLη op ξ)) p)

-- And the other direction.
-- Every formula in the closure is reached by the algorithm.
closure-complete : ∀ {At} (ξ : μML At 0) {ϕ : μML At 0}
                 → (ϕ ∈-Closure ξ) → (ϕ ∈ closure ξ)
closure-complete ξ ε = here refl
closure-complete (μML₁ op ξ) (down .op .ξ ◅ pxs) = there (node1 (closure-complete ξ pxs))
closure-complete (μML₂ op ξl ξr) (left .op .ξl .ξr ◅ pxs) = there (node2l (closure-complete ξl pxs))
closure-complete (μML₂ op ξl ξr) (right .op .ξl .ξr ◅ pxs) = there (node2r (closure-complete ξr pxs))
closure-complete (μMLη op ξ) (thru .(μMLη op ξ) {{fp}} ◅ pxs) = there (nodeη (closure-complete _ pxs))


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

expand-lookup-here : ∀ {At n} {ϕ : μML At n} {Γ : Scope At n} {t : Tree (μML At 0) n} {Δ : R.Scope (μML At 0) n}
                  → (p : Coh ϕ t) (ps : ScCoh Γ Δ)
                  → expand' Γ (injectL ϕ) ≡ R.head Δ t
expand-lookup-here var ps = {!!}
expand-lookup-here leaf ps = {!!}
expand-lookup-here (node1 p) ps = {!!}
expand-lookup-here (node2 p p₁) ps = {!!}
expand-lookup-here (nodeη p) ps = {!!}

bisim-head : ∀ {At n} {Γ : Scope At n} {Δ : R.Scope (μML At 0) n}
           → (ps : ScCoh Γ Δ) → (ξ : μML At n) → expand Γ ξ ≡ R.head Δ (rational-closure Γ ξ)
bisim-head Γ≈Δ (μML₀ _) = refl
bisim-head Γ≈Δ (μML₁ _ _) = refl
bisim-head Γ≈Δ (μML₂ _ _ _) = refl
bisim-head Γ≈Δ (μMLη _ _) = refl
bisim-head {Γ = ϕ ,- Γ} {Δ = t ,- Δ} (p ,- ps) (var F.zero) = expand-lookup-here p ps
bisim-head {Γ = ϕ ,- Γ} {Δ = t ,- Δ} (p ,- ps) (var (F.suc x)) = {!!}

-- We can't get away with only considering empty contexts, because we do need to traverse binders.
-- But the coinductive closure algorithm is only defined on sentences, so we cant plug arbitrary subformulas in there.
-- Lets try with the expansion map...it may even work...
rational-closure-unfolding-bisim : ∀ {At n} {Γ : Scope At n} {Δ : R.Scope (μML At 0) n}
                                  → ScCoh Γ Δ → (ξ : μML At n) → closure (expand Γ ξ) ~ R.unfold Δ (rational-closure Γ ξ)
T.head (rational-closure-unfolding-bisim Γ≈Δ ξ) = bisim-head Γ≈Δ ξ
T.tree (rational-closure-unfolding-bisim Γ≈Δ ξ) = {!!}

-- force (rational-closure-unfolding-bisim Γ (μML₀ op)) = leaf refl
-- force (rational-closure-unfolding-bisim Γ (μML₁ op ϕ)) = node1 refl (rational-closure-unfolding-bisim Γ ϕ)
-- force (rational-closure-unfolding-bisim Γ (μML₂ op ϕl ϕr)) = node2 refl (rational-closure-unfolding-bisim Γ ϕl) (rational-closure-unfolding-bisim Γ ϕr)
-- force (rational-closure-unfolding-bisim {At} {n} {Γ} {Δ} p (μMLη op ϕ)) = nodeη refl {!rational-closure-unfolding-bisim!}
-- force (rational-closure-unfolding-bisim Γ (var x)) = {!x!}

-- If the context is empty, then the expansion map is the identity, so we get the statement we wanted all along.
rational-closure-unfolding-bisim-sentence : ∀ {At} (ξ : μML At 0) → closure ξ ~ R.unfold R.[] (rational-closure [] ξ)
rational-closure-unfolding-bisim-sentence ξ = {!rational-closure-unfolding-bisim [] ξ!} -- rational-closure-unfolding-bisim [] ξ


-- The set of formulas in the closure is finite. todo: might want a different notion of finiteness.
-- Hopefully this should follow via some reasoning about the above.
closure-finite : ∀ {At} (ξ : μML At 0) → Σ[ n ∈ ℕ ] Closure ξ ≃ Fin n
closure-finite ξ = {!!}

