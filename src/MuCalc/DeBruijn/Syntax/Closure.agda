
module MuCalc.DeBruijn.Syntax.Closure where

open import Algebra.Structures.Propositional
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin)
open import Data.Vec
open import Data.Product
open import MuCalc.DeBruijn.Base hiding (¬)
open import MuCalc.DeBruijn.Guarded
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- Would have liked to have scopes be not just a nat, but rather
-- a vector of fixpoint formulas, so that variables can point directly
-- to the formula that bound it. But this would require μMLε to ultimately be
-- indexed by itself. Random idea --- in general, such types would loop the type
-- checker, but is there a type theory with decidable type-checking where they are
-- allowed, maybe in some restricted form? ie, a theory for graph-like terms, or
-- rather (spanning-tree-plus-backedges)-like terms?

mutual
  data μMLε (At : Set) (n : ℕ) : Set where
    var : (x : Fin n) → μMLε At n
    μML₀ : (op : Op₀ At) → μMLε At n
    μML₁ : (op : Op₁) → (ϕ : μMLε At n) → μMLε At n
    μML₂ : (op : Op₂) → (ϕ : μMLε At n) → (ψ : μMLε At n) → μMLε At n
    μMLη : (op : Opη) → (ϕ : μMLε At (suc n)) → μMLε At n
    ε : (x : Fin n) → μMLε At n

  data IsFPε {At : Set} : {n : ℕ} → μMLε At n → Set where
    fp : ∀ {n} → (op : Opη) (ϕ : μMLε At (suc n)) → IsFPε (μMLη op ϕ)


-- The subformula relation; paths through the trees.
-- Todo: change to ⊒ to match the closure graph convention below?
data _⊑_ {At : Set} : {i j : ℕ} → (ψ : μMLε At i) (ϕ : μMLε At j) → {{i ≤ j}} → Set where
  here  : ∀ {i} {ψ ϕ : μMLε At i} → ψ ≡ ϕ → (ψ ⊑ ϕ) {{≤-refl}}
  down  : ∀ op {i j} {p : i ≤ j} {ψ : μMLε At i} {ϕ : μMLε At j} → (ψ ⊑ ϕ) {{p}} → (ψ ⊑ (μML₁ op ϕ)) {{p}}
  left  : ∀ op {i j} {p : i ≤ j} {ψ : μMLε At i} {ϕˡ ϕʳ : μMLε At j} → (ψ ⊑ ϕˡ) {{p}} → (ψ ⊑ (μML₂ op ϕˡ ϕʳ)) {{p}}
  right : ∀ op {i j} {p : i ≤ j} {ψ : μMLε At i} {ϕˡ ϕʳ : μMLε At j} → (ψ ⊑ ϕʳ) {{p}} → (ψ ⊑ (μML₂ op ϕˡ ϕʳ)) {{p}}
  under : ∀ op {i j} {p : i ≤ j} {ψ : μMLε At i} {ϕ : μMLε At (suc j)} → (ψ ⊑ ϕ) {{m≤n⇒m≤1+n p}} → (ψ ⊑ (μMLη op ϕ)) {{p}}

-- Setup for sorted lists/sets of formulas.
-- These postulats are trivial but really annoying to do manually. need some "deriving" metaprogram...
postulate _<ε_ : {At : Set} {n : ℕ} → (ϕ ψ : μMLε At n) → Set
postulate <ε-STO : (At : Set) {n : ℕ} → IsPropStrictTotalOrder {μMLε At n} _≡_ _<ε_
open import Data.FreshList.InductiveInductive
open import Free.IdempotentCommutativeMonoid.Base
open import Free.IdempotentCommutativeMonoid.Properties


unfoldε : {At : Set} {n : ℕ}
        → {ϕ' : μMLε At n} (ϕ : IsFPε ϕ') -- the original formula
        → μMLε At n
unfoldε (fp op ϕ) = {!!}

-- The closure relation.
-- Only defined on closed formulas for now, though an "open closure"
-- notion could be interesting. What sort of compositional structure
-- is there?
data _~C~>_ {At : Set} : (ϕ ψ : μMLε At 0) → Set where
  down   : (op : Op₁) (ϕ : μMLε At 0)   → μML₁ op ϕ ~C~> ϕ
  left   : (op : Op₂) (ϕ ψ : μMLε At 0) → μML₂ op ϕ ψ ~C~> ϕ
  right  : (op : Op₂) (ϕ ψ : μMLε At 0) → μML₂ op ϕ ψ ~C~> ψ
  unfold : (op : Opη) {ϕ' : μMLε At 0} (ϕ : IsFPε ϕ') → unfoldε ϕ ~C~> ϕ'
