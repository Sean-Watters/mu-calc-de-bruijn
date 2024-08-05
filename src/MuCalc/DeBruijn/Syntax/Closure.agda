
module MuCalc.DeBruijn.Syntax.Closure where

open import Algebra.Structures.Propositional
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin; fromℕ; fold) renaming (zero to fzero; suc to fsuc)
open import Data.Vec hiding ([_])
open import Data.Product
open import MuCalc.DeBruijn.Base hiding (¬; sub₀; _[_]) renaming (unfold to unfold')
open import MuCalc.DeBruijn.Guarded
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.Isomorphism
open import Relation.Nullary

-- Would have liked to have scopes be not just a nat, but rather
-- a vector of fixpoint formulas, so that variables can point directly
-- to the formula that bound it. But this would require μMLε to ultimately be
-- indexed by itself. Random idea --- in general, such types would loop the type
-- checker, but is there a type theory with decidable type-checking where they are
-- allowed, maybe in some restricted form? ie, a theory for graph-like terms, or
-- rather (spanning-tree-plus-backedges)-like terms?

module AttemptOne where
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
  -- These postulates are trivial but really annoying to do manually. need some "deriving" metaprogram...
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
    unfold : {ϕ' : μMLε At 0} (ϕ : IsFPε ϕ') → ϕ' ~C~> unfoldε ϕ


-- No dummies, trying to track binder formulae in the indices instead
module AttemptTwo where
  -- Vectors of fixpoint formulas, with the extra trick that the number of
  -- free variables allowed depends on its position in the vector
  data Scope (At : Set) : ℕ → Set where
    [] : Scope At zero
    _-,_ : ∀ {n} → (Γ₀ : Scope At n) → {ϕ : μML At n} (Γ₀ : IsFP ϕ) → Scope At (suc n)

  -- Sublimely-scoped formulas
  mutual
    data μMLε (At : Set) {n : ℕ} (Γ : Scope At n) : Set where
      var : (x : Fin n) → μMLε At Γ
      μML₀ : (op : Op₀ At) → μMLε At Γ
      μML₁ : (op : Op₁) → (ϕ : μMLε At Γ) → μMLε At Γ
      μML₂ : (op : Op₂) → (ϕ : μMLε At Γ) → (ψ : μMLε At Γ) → μMLε At Γ
      μMLη : (op : Opη) → {ψ : μML At (suc n)} → (ϕ : μMLε At (Γ -, fp op ψ)) → ψ ≈ ϕ → μMLε At Γ

    data _≈_ {At : Set} {n : ℕ} {Γ : Scope At n} : μML At n → μMLε At Γ → Set where
      var  : (x : Fin n) → (var x) ≈ (var x)
      μML₀ : (op : Op₀ At) → μML₀ op ≈ μML₀ op
      μML₁ : (op : Op₁)
           → {ϕ : μML At n} {ϕ' : μMLε At Γ} → ϕ ≈ ϕ'
           → μML₁ op ϕ ≈ μML₁ op ϕ'
      μML₂ : (op : Op₂)
           → {ϕ : μML At n} {ϕ' : μMLε At Γ} → ϕ ≈ ϕ'
           → {ψ : μML At n} {ψ' : μMLε At Γ} → ψ ≈ ψ'
           → μML₂ op ϕ ψ ≈ μML₂ op ϕ' ψ'
      μMLη : (op : Opη)
           → {ϕ : μML At (suc n)} {ϕ' : μMLε At (Γ -, fp op ϕ)} → (p : ϕ ≈ ϕ')
           → μMLη op ϕ ≈ μMLη op ϕ' p

  data IsFPε {At : Set} : {n : ℕ} {Γ : Scope At n} → μMLε At Γ → Set where
    fp : ∀ {n} {Γ : Scope At n} → (op : Opη) {ψ : μML At (suc n)} (ϕ : μMLε At (Γ -, fp op ψ)) (p : ψ ≈ ϕ) → IsFPε (μMLη op ϕ p)

  -- We can downwardly traverse a formula and annotate it with the scope infomation as long
  -- as we have an annotated scope for everything "above" it in the sf tree.
  recompute-scope : ∀ {At : Set} {n : ℕ} → μML At n → (Γ : Scope At n) → μMLε At Γ
  recompute-scope-eq : ∀ {At : Set} {n : ℕ} (ϕ : μML At n) (Γ : Scope At n) → ϕ ≈ recompute-scope ϕ Γ
 
  recompute-scope (var x) Γ = var x
  recompute-scope (μML₀ op) Γ = μML₀ op
  recompute-scope (μML₁ op ϕ) Γ with recompute-scope ϕ Γ
  ... | ϕ' = μML₁ op ϕ'
  recompute-scope (μML₂ op ϕ ψ) Γ with recompute-scope ϕ Γ | recompute-scope ψ Γ
  ... | ϕ' | ψ' = μML₂ op ϕ' ψ'
  recompute-scope (μMLη op ϕ) Γ with recompute-scope ϕ (Γ -, fp op ϕ) in eq
  ... | ϕ' = μMLη op ϕ' (subst (ϕ ≈_) eq (recompute-scope-eq ϕ (Γ -, fp op ϕ)))
 
  recompute-scope-eq (var x) Γ = var x
  recompute-scope-eq (μML₀ op) Γ = μML₀ op
  recompute-scope-eq (μML₁ op ϕ) Γ = μML₁ op (recompute-scope-eq ϕ Γ)
  recompute-scope-eq (μML₂ op ϕ ϕ₁) Γ = μML₂ op (recompute-scope-eq ϕ Γ) (recompute-scope-eq ϕ₁ Γ)
  recompute-scope-eq (μMLη op ϕ) Γ = μMLη op (recompute-scope-eq ϕ (Γ -, fp op ϕ))

  -- And of course, we can throw our richer scope away.
  forget-scope : ∀ {At : Set} {n : ℕ} {Γ : Scope At n} → μMLε At Γ → μML At n
  forget-scope (var x) = var x
  forget-scope (μML₀ op) = μML₀ op
  forget-scope (μML₁ op ϕ) = μML₁ op (forget-scope ϕ)
  forget-scope (μML₂ op ϕ ψ) = μML₂ op (forget-scope ϕ) (forget-scope ψ)
  forget-scope (μMLη op ϕ p) = μMLη op (forget-scope ϕ)

  forget-scope-fp : ∀ {At : Set} {n : ℕ} {Γ : Scope At n} {ϕ : μMLε At Γ} → IsFPε ϕ → IsFP (forget-scope ϕ)
  forget-scope-fp (fp op ϕ p) = {!!}


  -- Open terms are open graphs! In the well-scoped world, the scope only tells us how many backedges were chopped off,
  -- so there are many ways to close the term. But with the "sublime" scopes, there is 1 unique way to close the term
  -- (starting from a μ/ν, at lease; we can always put more propositional/modal stuff above that).
  -- This means that for every choice of scope Γ, we have the following isomorphism:

  sublime-iso : {At : Set} {n : ℕ} {Γ : Scope At n} → μML At n ≃ μMLε At Γ
  sublime-iso = ?

  ------------------------------------------------------------------
  -- The example family of formulas (prop 10 of the LIPICS paper) --
  ------------------------------------------------------------------
  formulafam-β₀ : (At : Set) (n : ℕ) → μML At n
  formulafam-β₀ At n = μMLη mu (fold (μML At) (λ {n = n} ϕ → μML₂ and (var (fromℕ n)) (inject₁ ϕ)) (var fzero) (fromℕ n))


  formulafam-α : (At : Set) (n : ℕ) (i j : Fin n) → μML At n
  formulafam-β' : (At : Set) (n : ℕ) → (i : Fin n) → μML At n

  formulafam-α At n i j = {!!}
  formulafam-β' At n i = {!!}


  postulate _<ε_ : {At : Set} {n : ℕ} {Γ : Scope At n} → (ϕ ψ : μMLε At Γ) → Set
  postulate <ε-STO : (At : Set) {n : ℕ} {Γ : Scope At n} → IsPropStrictTotalOrder {μMLε At Γ} _≡_ _<ε_
  open import Data.FreshList.InductiveInductive
  open import Free.IdempotentCommutativeMonoid.Base
  open import Free.IdempotentCommutativeMonoid.Properties

  -- If we were to try to naively replicate the implementation of substitution and unfolding here, we'd be
  -- restricted (specifically in the implementation of subst extension) by how prescriptive our scopes are.
  -- So instead, we just directly use the isomorphism. Which, besides, is neater.
  unfold : ∀ {At n} {Γ : Scope At n} {ϕ : μMLε At Γ} → IsFPε ϕ → μMLε At Γ
  unfold {Γ = Γ} ϕ = recompute-scope (unfold' (forget-scope-fp ϕ)) Γ

{-
  -- Towards substitution (standard stuff from PLFA) --

  -- Re-scoping, defined mutually with the proof that it respects ≈
  rescope : ∀ {n m At} {Γ : Scope At n} {Δ : Scope At m}
         → (Fin n → Fin m) -- if we have an embedding of Γ into Δ...
         → μMLε At Γ → μMLε At Δ -- then we can rescope Γ-terms to be Δ-terms
  rescope-resp-≈ : ∀ {n m At} {Γ : Scope At n} {Δ : Scope At m}
                 → (ρ : Fin n → Fin m)
                 → {ψ : μML At n} {ϕ : μMLε At Γ}
                 → ψ ≈ ϕ
                 → _≈_ {At} {m} {Δ} (rescope' ρ ψ) (rescope ρ ϕ)

  rescope ρ (var x) = var (ρ x)
  rescope ρ (μML₀ op) = μML₀ op
  rescope ρ (μML₁ op ϕ) = μML₁ op (rescope ρ ϕ)
  rescope ρ (μML₂ op ϕ ψ) = μML₂ op (rescope ρ ϕ) (rescope ρ ψ)
  rescope ρ (μMLη op {ψ} ϕ p) = μMLη op {rescope' (ext ρ) ψ} (rescope (ext ρ) ϕ) (rescope-resp-≈ (ext ρ) p)

  rescope-resp-≈ ρ (var x) = var (ρ x)
  rescope-resp-≈ ρ (μML₀ op) = μML₀ op
  rescope-resp-≈ ρ (μML₁ op p) = μML₁ op (rescope-resp-≈ ρ p)
  rescope-resp-≈ ρ (μML₂ op p p₁) = μML₂ op (rescope-resp-≈ ρ p) (rescope-resp-≈ ρ p₁)
  rescope-resp-≈ ρ (μMLη op p) = μMLη op (rescope-resp-≈ (ext ρ) p)

  -- Parallel substitutions are maps from variables to formulae.
  Subst : {At : Set} (n : ℕ) {m : ℕ} (Δ : Scope At m) → Set
  Subst {At} n Δ = Fin n → μMLε At Δ

  -- We can forget the backedges from the scope to recover substitutions on simple scopes
  forget-subst : ∀ {At n m} {Δ : Scope At m}
               → Subst n Δ → Subst' At n m
  forget-subst σ x = forget-scope (σ x)

  -- Substitution extension.
  -- Note that due to the restictiveness of our scopes, we need Γ and Δ to have the same size
  -- BUT THIS IS A REAL PROBLEM AND NEEDS FIXED
  exts : ∀ {At n} {Δ : Scope At n}
       → {ϕ' : μML At n} (ϕ : IsFP ϕ')
       → Subst n Δ → Subst (suc n) (Δ -, ϕ)
  exts ϕ σ fzero = var fzero
  exts ϕ σ (fsuc x) = rescope fsuc (σ x)

  sub : ∀ {At n} {Γ Δ : Scope At n} → Subst n Δ → μMLε At Γ → μMLε At Δ
  sub σ (var x) = σ x
  sub σ (μML₀ op) = μML₀ op
  sub σ (μML₁ op ϕ) = μML₁ op (sub σ ϕ)
  sub σ (μML₂ op ϕ ψ) = μML₂ op (sub σ ϕ) (sub σ ψ)
  sub σ (μMLη op {ψ} ϕ  p) = μMLη op {sub' (exts' (forget-subst σ)) ψ} (sub (exts _ σ) ϕ) {!!} -- there may be a less gnarly way to set this up? maybe by changing the order of some extensions and forgets

  -- Single substitution is a special case of parallel substitution
  sub₀ : ∀ {At n} {Γ : Scope At n} → μMLε At Γ → Subst (suc n) Γ
  sub₀ ϕ fzero = ϕ -- at 0 we substitute
  sub₀ ϕ (fsuc x) = var x -- elsewhere we leave step the variable

  _[_] : ∀ {At n} {Γ : Scope At n} {ϕ' : μML At n} {ϕ : IsFP ϕ'} → μMLε At (Γ -, ϕ) → μMLε At Γ → μMLε At Γ
  _[_] {At} {n} ϕ ξ = sub {!sub₀!} {!!} -- but here is where forcing Γ and Δ to have the same length is a real problem...

-}

  -- The subformula tree. Identification of equal subformulas in different branches yields the sf dag,
  -- and replacement of variables with backedges yields the closure graph?
  -- Does this smell ok? Diversion --- look at the example that gives exponential difference between closure and sf,
  -- and figure out what happens to that here.
  data ClosTree {At : Set} {n : ℕ} {Γ : Scope At n} : μMLε At Γ → Set where
    leaf  : ∀ {op} → ClosTree (μML₀ op)
    node₁ : ∀ {op ϕ} → ClosTree ϕ → ClosTree (μML₁ op ϕ)
    node₂ : ∀ {op ϕ ψ} → ClosTree ϕ → ClosTree ψ → ClosTree (μML₂ op ϕ ψ)
    nodeη : ∀ {op ψ ϕ} → (p : ψ ≈ ϕ) → ClosTree ϕ → ClosTree (μMLη op ϕ p)
    back : ∀ {x} → ClosTree (var x) -- variables store pointers back to their binders, and so indicate backedges
