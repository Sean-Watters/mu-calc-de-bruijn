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
open import Codata.NWFTree as T


----------------
-- Tree Stuff --
----------------


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

-- Computing the closure as a via the expansion map applied to the subformulas, represented as an
-- inductive approximation of a rational tree.
rational-closure : ∀ {At n} (Γ : Scope At n) (ϕ : μML At n) → R.Tree (μML At 0) n
rational-closure Γ ξ@(var x) = loop x
rational-closure Γ ξ@(μML₀ op) = leaf (expand Γ ξ)
rational-closure Γ ξ@(μML₁ op ϕ) = node1 op (expand Γ ξ) (rational-closure Γ ϕ)
rational-closure Γ ξ@(μML₂ op ϕl ϕr) = node2 op (expand Γ ξ) (rational-closure Γ ϕl) (rational-closure Γ ϕr)
rational-closure Γ ξ@(μMLη op ϕ) = nodeη op (expand Γ ξ) (rational-closure (ξ ,- Γ) ϕ)

-- A relation witnessing whether a rational tree represents the closure of a formula,
-- via the expansion-of-subforumulas approach.
data IsClosure {At : Set} {n : ℕ} (Γ : Scope At n) : μML At n → R.Tree (μML At 0) n → Set where
  loop : (x : Fin n) → IsClosure Γ (var x) (loop x)
  leaf : ∀ op → IsClosure Γ (μML₀ op) (leaf (μML₀ op))
  node1 : ∀ op (ϕ : μML At n) (t : R.Tree (μML At 0) n) → IsClosure Γ ϕ t → IsClosure Γ (μML₁ op ϕ) (node1 op (expand Γ (μML₁ op ϕ)) t)
  node2 : ∀ op (ϕl ϕr : μML At n) (tl tr : R.Tree (μML At 0) n) → IsClosure Γ ϕl tl → IsClosure Γ ϕr tr → IsClosure Γ (μML₂ op ϕl ϕr) (node2 op (expand Γ (μML₂ op ϕl ϕr)) tl tr)
  nodeη : ∀ op (ϕ : μML At (suc n)) (t : R.Tree (μML At 0) (suc n)) → IsClosure ((μMLη op ϕ) ,- Γ) ϕ t → IsClosure Γ (μMLη op ϕ) (nodeη op (expand Γ (μMLη op ϕ)) t)

-- Coherence between scopes of formulas and scopes of rational trees.
data ScCoh {At : Set} : ∀ {n} → Scope At n → R.Scope (μML At 0) n → Set where
  [] : ScCoh [] []
  _,-_ : ∀ {n} {Γ : Scope At n} {Γ₀ : μML At n} {{_ : IsFP Γ₀}} {Δ : R.Scope (μML At 0) n} {Δ₀ : R.Tree (μML At 0) n}
       → IsClosure Γ Γ₀ Δ₀ → ScCoh Γ Δ → ScCoh (Γ₀ ,- Γ) (Δ₀ ,- Δ)

-- The rational tree produced has the same shape as the formula
rational-closure-IsClosure : ∀ {At n} (Γ : Scope At n) (ϕ : μML At n) → IsClosure Γ ϕ (rational-closure Γ ϕ)
rational-closure-IsClosure Γ (var x) = loop x
rational-closure-IsClosure Γ (μML₀ op) = leaf op
rational-closure-IsClosure Γ (μML₁ op ϕ) = node1 op ϕ (rational-closure Γ ϕ) (rational-closure-IsClosure Γ ϕ)
rational-closure-IsClosure Γ (μML₂ op ϕl ϕr) = node2 op ϕl ϕr (rational-closure Γ ϕl) (rational-closure Γ ϕr)
                                                (rational-closure-IsClosure Γ ϕl) (rational-closure-IsClosure Γ ϕr)
rational-closure-IsClosure Γ (μMLη op ϕ) = nodeη op ϕ (rational-closure (μMLη op ϕ ,- Γ) ϕ)
                                            (rational-closure-IsClosure (μMLη op ϕ ,- Γ) ϕ)



expandvar-head : ∀ {At n} {Γ : Scope At n} {Δ : R.Scope (μML At 0) n} (p : Plus n 0 n) (x : Fin n)
               → ScCoh Γ Δ
               → expand-var Γ (split p (injectL p x)) ≡ R.head Δ (loop x)
expandvar-head (sucl p) F.zero (nodeη op ϕ t q ,- qs)
  = cong (μMLη op) (expand'-thin _ ϕ (plus _ 0) idr (sym $ +-identityʳ _) refl)
expandvar-head {Γ = Γ₀ ,- Γ} (sucl p) (F.suc x) (x₁ ,- qs) = trans (expandvar-extend Γ Γ₀ (split p (injectL p x))) (expandvar-head p x qs)


rclos-bisim-head : ∀ {At n} {Γ : Scope At n} {Δ : R.Scope (μML At 0) n}
           → (ps : ScCoh Γ Δ) (p : Plus n 0 n) (ξ : μML At n) → expand' p Γ (thin p ξ) ≡ R.head Δ (rational-closure Γ ξ)
rclos-bisim-head Γ≈Δ p (μML₀ op) = refl
rclos-bisim-head Γ≈Δ p (μML₁ op ϕ)
  rewrite Plus-irrelevant p idr = refl
rclos-bisim-head Γ≈Δ p (μML₂ op ϕl ϕr)
  rewrite Plus-irrelevant p idr = refl
rclos-bisim-head Γ≈Δ p (μMLη op ϕ)
  rewrite Plus-irrelevant p idr = refl
rclos-bisim-head Γ≈Δ p (var x) = expandvar-head p x Γ≈Δ

-- We can't get away with only considering empty contexts, because we do need to traverse binders.
-- But the coinductive closure algorithm is only defined on sentences, so we cant plug arbitrary subformulas in there.
-- Lets try with the expansion map...it may even work...
rclos-bisim : ∀ {At n} {Γ : Scope At n} {Δ : R.Scope (μML At 0) n}
            → ScCoh Γ Δ → (p : Plus n 0 n) → (ξ : μML At n)
            → closure (expand' p Γ (thin p ξ)) ~ R.unfold Δ (rational-closure Γ ξ)
rclos-bisim-tree : ∀ {At n} {Γ : Scope At n} {Δ : R.Scope (μML At 0) n}
                 → ScCoh Γ Δ → (p : Plus n 0 n) → (ξ : μML At n)
                 → Pointwise _≡_ (∞NWFTree.tree (closure (expand' p Γ (thin p ξ)))) (R.tree Δ (rational-closure Γ ξ))

rclos-bisim-tree Γ≈Δ p (μML₀ op) = leaf
rclos-bisim-tree Γ≈Δ p (μML₁ op ξ) = node1 (rclos-bisim Γ≈Δ p ξ)
rclos-bisim-tree Γ≈Δ p (μML₂ op ξl ξr) = node2 (rclos-bisim Γ≈Δ p ξl) (rclos-bisim Γ≈Δ p ξr)
rclos-bisim-tree {At} {n} {Γ} {Δ} Γ≈Δ p (μMLη op ξ) = nodeη pf where
    open T.bisim-Reasoning (μML At 0)
    pf =
      begin
        closure (unfold (μMLη op (expand' (sucr p) Γ (thin (sucl p) ξ))))
      ≡⟨ cong closure
              (unfold-expand op Γ (thin (sucl p) ξ) (sucr p) (sucl p)) ⟩ -- todo: unfold-expand not implemented yet
        closure (expand' (sucl p) (μMLη op (thin (sucl p) ξ) ,- Γ) (thin (sucl p) ξ))
      ≡⟨ cong (λ z → closure (expand' (sucl p) (μMLη op z ,- Γ) (thin (sucl p) ξ)))
              (thin-sucl p ξ) ⟩
        closure (expand' (sucl p) (μMLη op ξ ,- Γ) (thin (sucl p) ξ))
      ≈⟨ rclos-bisim (rational-closure-IsClosure Γ (μMLη op ξ) ,- Γ≈Δ) (sucl p) ξ ⟩
        R.unfold (nodeη op (expand Γ (μMLη op ξ)) (rational-closure (μMLη op ξ ,- Γ) ξ) ,- Δ) (rational-closure (μMLη op ξ ,- Γ) ξ)
      ∎

rclos-bisim-tree {Γ = ϕ ,- Γ} {t ,- Δ} (cl ,- Γ≈Δ) p (var F.zero) = {!!}
rclos-bisim-tree {At} {Γ = ϕ ,- Γ} {t ,- Δ} (cl ,- Γ≈Δ) (sucl p) (var (F.suc x)) = {!rclos-bisim-tree Γ≈Δ p (var x)!} where open T.bisim-Reasoning (μML At 0)

rclos-bisim Γ≈Δ p ξ .∞Pointwise.head = rclos-bisim-head Γ≈Δ p ξ
rclos-bisim Γ≈Δ p ξ .∞Pointwise.tree = rclos-bisim-tree Γ≈Δ p ξ



-- If the context is empty, then the expansion map is the identity, so we get the statement we wanted all along.
rclos-bisim-sentence : ∀ {At} (ξ : μML At 0) → closure ξ ~ R.unfold R.[] (rational-closure [] ξ)
rclos-bisim-sentence {At} ξ =
  begin
    closure ξ
  ≡⟨ (cong closure (expand-empty ξ)) ⟩
    closure (expand [] ξ)
  ~⟨ (rclos-bisim [] idr ξ) ⟩
    R.unfold [] (rational-closure [] ξ)
  ∎ where open T.bisim-Reasoning (μML At 0)

-- The closure is bisimilar to the unfolding of a finite tree, so it must contain a finite number of unique formulas.
-- (ie, exactly those that appear in the tree)

------------------
-- Closure Size --
------------------

-- The closure size is the number of *unique* formulas in the rational closure tree-with-backedges.
-- Note that because this is a tree with backedges, there is no cross-branch sharing, so there may be duplicate nodes.
-- Counting these would (potentially exponentially) over-estimate the closure size.
closure-size : ∀ {At} (ξ : μML At 0) → ℕ
closure-size ξ = {!!}

-- If we didn't over-estimate the closure size when counting the tree, then we can prove that this
-- really is the size of the closure set.
closure-finite : ∀ {At} (ξ : μML At 0) → Closure ξ ≃ Fin (closure-size ξ)
closure-finite ξ = {!!}
