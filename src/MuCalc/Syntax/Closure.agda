{-# OPTIONS --guardedness --rewriting #-}
module MuCalc.Syntax.Closure where

open import Data.Bool using (Bool; true; false)
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties
open import Data.Fin as F using (Fin) renaming (_ℕ-ℕ_ to _-_)
open import Data.Fin.Renaming
open import Data.Product
open import Data.Sum

open import Function using (id; _$_; _∘_)

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.Isomorphism
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star

open import MuCalc.Base
open import MuCalc.Syntax.ExpansionMap
open import MuCalc.Syntax.Substitution

open import Rational.Tree as R hiding (Scope; rename; lookup; unfold)
open import Rational.Tree.Properties using (∞bisim-unfold-any→; ∞bisim-unfold-any←)
open import Codata.NWFTree as T

-- Rewrite rules
-- open import Rewrite.Plus

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
                → (ϕ T.∈ closure ξ) → (ϕ ∈-Closure ξ)
closure-sound ξ (here refl) = ε
closure-sound (μML₁ op ξ) (there (node1 p)) = down op ξ ◅ (closure-sound ξ p)
closure-sound (μML₂ op ξl ξr) (there (node2l p)) = left  op ξl ξr ◅ (closure-sound ξl p)
closure-sound (μML₂ op ξl ξr) (there (node2r p)) = right op ξl ξr ◅ (closure-sound ξr p)
closure-sound (μMLη op ξ) (there (nodeη p)) = thru (μMLη op ξ) ◅ (closure-sound (unfold (μMLη op ξ)) p)

-- And the other direction.
-- Every formula in the closure is reached by the algorithm.
closure-complete : ∀ {At} (ξ : μML At 0) {ϕ : μML At 0}
                 → (ϕ ∈-Closure ξ) → (ϕ T.∈ closure ξ)
closure-complete ξ ε = T.here refl
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
rational-closure Γ ξ@(var x) = var x
rational-closure Γ ξ@(μML₀ op) = step (expand Γ ξ) leaf
rational-closure Γ ξ@(μML₁ op ϕ) = step (expand Γ ξ) (node1 op (rational-closure Γ ϕ))
rational-closure Γ ξ@(μML₂ op ϕl ϕr) = step (expand Γ ξ) (node2 op (rational-closure Γ ϕl) (rational-closure Γ ϕr))
rational-closure Γ ξ@(μMLη op ϕ) = step (expand Γ ξ) (nodeη op (rational-closure (ξ ,- Γ) ϕ))

---------------------------------
-- Relating Formulas and Trees --
---------------------------------

-- A relation witnessing whether a rational tree represents the closure of a formula,
-- via the expansion-of-subforumulas approach.
data IsClosure {At : Set} {n : ℕ} (Γ : Scope At n) : μML At n → R.Tree (μML At 0) n → Set where
  loop : (x : Fin n) → IsClosure Γ (var x) (var x)
  leaf : ∀ op → IsClosure Γ (μML₀ op) (step (μML₀ op) leaf)
  node1 : ∀ op {ϕ : μML At n} {t : R.Tree (μML At 0) n} → IsClosure Γ ϕ t → IsClosure Γ (μML₁ op ϕ) (step (expand Γ (μML₁ op ϕ)) (node1 op t))
  node2 : ∀ op {ϕl ϕr : μML At n} {tl tr : R.Tree (μML At 0) n} → IsClosure Γ ϕl tl → IsClosure Γ ϕr tr → IsClosure Γ (μML₂ op ϕl ϕr) (step (expand Γ (μML₂ op ϕl ϕr)) (node2 op tl tr))
  nodeη : ∀ op {ϕ : μML At (suc n)} {t : R.Tree (μML At 0) (suc n)} → IsClosure ((μMLη op ϕ) ,- Γ) ϕ t → IsClosure Γ (μMLη op ϕ) (step (expand Γ (μMLη op ϕ)) (nodeη op t))

-- Coherence between scopes of formulas and scopes of rational trees.
data ScCoh {At : Set} : ∀ {n} → Scope At n → R.Scope (μML At 0) n → Set where
  [] : ScCoh [] []
  _,-_ : ∀ {n} {Γ : Scope At n} {Γ₀ : μML At n} {{_ : IsFP Γ₀}} {Δ : R.Scope (μML At 0) n} {Δ₀ : R.Tree (μML At 0) n} {{_ : NonVar Δ₀}}
       → IsClosure Γ Γ₀ Δ₀ → ScCoh Γ Δ → ScCoh (Γ₀ ,- Γ) (Δ₀ ,- Δ)

-- The rational tree produced has the same shape as the formula
rational-closure-IsClosure : ∀ {At n} (Γ : Scope At n) (ϕ : μML At n) → IsClosure Γ ϕ (rational-closure Γ ϕ)
rational-closure-IsClosure Γ (var x) = loop x
rational-closure-IsClosure Γ (μML₀ op) = leaf op
rational-closure-IsClosure Γ (μML₁ op ϕ) = node1 op (rational-closure-IsClosure Γ ϕ)
rational-closure-IsClosure Γ (μML₂ op ϕl ϕr) = node2 op (rational-closure-IsClosure Γ ϕl) (rational-closure-IsClosure Γ ϕr)
rational-closure-IsClosure Γ (μMLη op ϕ) = nodeη op (rational-closure-IsClosure (μMLη op ϕ ,- Γ) ϕ)

------------------------------
-- Proving the Bisimilarity --
------------------------------

expandvar-head : ∀ {At n} {Γ : Scope At n} {Δ : R.Scope (μML At 0) n} (x : Fin n)
               → ScCoh Γ Δ
               → expand-var Γ (F.splitAt 0 x) ≡ R.head Δ (var x)
expandvar-head {Γ = μMLη op ϕ ,- Γ} F.zero (nodeη op q ,- qs) = cong (μMLη op ∘ expand Γ) $
  begin
    rename (ext id) ϕ
  ≡⟨ rename-cong ext-id ϕ ⟩
    rename id ϕ
  ≡⟨ rename-id ϕ ⟩
    ϕ
  ∎ where open ≡-Reasoning
expandvar-head (F.suc x) (q ,- qs) = expandvar-head x qs

rclos-bisim-head : ∀ {At n} {Γ : Scope At n} {Δ : R.Scope (μML At 0) n}
                 → (ps : ScCoh Γ Δ) (ξ : μML At n)
                 → {t : R.Tree (μML At 0) n} → (cl : IsClosure Γ ξ t)
                 → expand Γ ξ ≡ R.head Δ t

rclos-bisim-head Γ≈Δ (μML₀ op) (leaf .op) = refl
rclos-bisim-head Γ≈Δ (μML₁ op ϕ) (node1 .op cl) = refl
rclos-bisim-head Γ≈Δ (μML₂ op ϕl ϕr) (node2 .op cll clr) = refl
rclos-bisim-head Γ≈Δ (μMLη op ϕ) (nodeη .op cl) = refl
rclos-bisim-head Γ≈Δ (var x) (loop .x) = expandvar-head x Γ≈Δ

-- We can't get away with only considering empty contexts, because we do need to traverse binders.
-- But the coinductive closure algorithm is only defined on sentences, so we cant plug arbitrary subformulas in there.
-- Lets try with the expansion map...it may even work...
rclos-bisim : ∀ {At n} {Γ : Scope At n} {Δ : R.Scope (μML At 0) n}
            → ScCoh Γ Δ → (ξ : μML At n)
            → {t : R.Tree (μML At 0) n} → (cl : IsClosure Γ ξ t)
            → closure (expand Γ ξ) ~ R.unfold Δ t

rclos-bisim-tree : ∀ {At n} {Γ : Scope At n} {Δ : R.Scope (μML At 0) n}
                 → ScCoh Γ Δ → (ξ : μML At n)
                 → {t : R.Tree (μML At 0) n} → (cl : IsClosure Γ ξ t)
                 → Pointwise _≡_ (∞NWFTree.tree (closure (expand Γ ξ))) (R.unfold-subtree Δ t)

rclos-bisim Γ≈Δ ξ cl .∞Pointwise.head = rclos-bisim-head Γ≈Δ ξ cl
rclos-bisim Γ≈Δ ξ cl .∞Pointwise.tree = rclos-bisim-tree Γ≈Δ ξ cl

rclos-bisim-tree Γ≈Δ (μML₀ op) (leaf .op) = leaf
rclos-bisim-tree Γ≈Δ (μML₁ op ξ) (node1 .op cl) = node1 (rclos-bisim Γ≈Δ ξ cl)
rclos-bisim-tree Γ≈Δ (μML₂ op ξl ξr) (node2 .op cll clr) = node2 (rclos-bisim Γ≈Δ ξl cll) (rclos-bisim Γ≈Δ ξr clr)
rclos-bisim-tree {At} {n} {Γ} {Δ} Γ≈Δ (μMLη op ξ) (nodeη .op cl)
  rewrite (cong closure (unfold-expand op Γ ξ))
  = nodeη (rclos-bisim (nodeη op cl ,- Γ≈Δ) ξ cl)

-- -- Very interesting - using this DSL style broke termination checking. Rewrite to the rescue!
-- -- Good thing we didn't need to chain bisim proofs together...
-- -- I guess the problem was nesting the DSL proof inside a larger proof.
-- = nodeη $
--     begin
--       closure (unfold (μMLη op (expand Γ ξ)))
--     ≡⟨ cong closure (unfold-expand op Γ ξ) ⟩
--       closure (expand (μMLη op ξ ,- Γ) ξ)
--     ≈⟨ rclos-bisim (nodeη op cl ,- Γ≈Δ) ξ cl ⟩
--       R.unfold (nodeη op (expand Γ (μMLη op ξ)) _ ,- Δ) _
--     ∎ where open T.bisim-Reasoning (μML At 0)


rclos-bisim-tree {Γ = Γ₀ ,- Γ} {Δ = Δ₀ ,- Δ} (cl ,- Γ≈Δ) (var F.zero) (loop .F.zero)
  rewrite rename-id Γ₀
  = rclos-bisim-tree Γ≈Δ Γ₀ cl
rclos-bisim-tree (cl ,- Γ≈Δ) (var (F.suc x)) (loop .(F.suc x)) = rclos-bisim-tree Γ≈Δ (var x) (loop x)


-- If the context is empty, then the expansion map is the identity, so we get the statement we wanted all along.
rclos-bisim-sentence : ∀ {At} (ξ : μML At 0) → closure ξ ~ R.unfold R.[] (rational-closure [] ξ)
rclos-bisim-sentence {At} ξ =
  begin
    closure ξ
  ≡⟨  cong closure (expand-nil ξ)  ⟩
    closure (expand [] ξ)
  ~⟨  rclos-bisim [] ξ (rational-closure-IsClosure [] ξ)  ⟩
    R.unfold [] (rational-closure [] ξ)
  ∎ where open T.bisim-Reasoning (μML At 0)

----------------------------------------------------
-- Correctness for the Rational Closure Algorithm --
----------------------------------------------------

{-
We have a coinductive closure algorithm (`closure`) that was easy to prove correct (via
`closure-sound` and `closure-complete`).

We have an inductive approximation of the closure as a tree with backedges represented as
variables (`rational-closure`) --- it is finite by construction.

We have proved that `closure` is bisimilar to the "unfolding" of `rational-closure` to an
infinite cotree.

We can now show that the finite algorithm is also correct, by transporting across the bisimulation.
-}

-- Every formula produced by the rational closure algorithm really is in the closure.
rational-closure-sound : ∀ {At} (ξ : μML At 0) {ϕ : μML At 0}
                       → (ϕ R.∈ (rational-closure [] ξ)) → (ϕ ∈-Closure ξ)
rational-closure-sound ξ p = closure-sound ξ (∞bisim-unfold-any← (rclos-bisim-sentence ξ) p)

-- Every formula in the closure is reached by the algorithm.
rational-closure-complete : ∀ {At} (ξ : μML At 0) {ϕ : μML At 0}
                          → (ϕ ∈-Closure ξ) → (ϕ R.∈ (rational-closure [] ξ))
rational-closure-complete ξ p = ∞bisim-unfold-any→ (rclos-bisim-sentence ξ) (closure-complete ξ p)
