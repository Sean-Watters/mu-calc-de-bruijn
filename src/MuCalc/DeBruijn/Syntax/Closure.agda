{-# OPTIONS --guardedness #-}
module MuCalc.DeBruijn.Syntax.Closure where

open import Algebra.Structures.Propositional
open import Data.Nat
open import Data.Nat.Properties using (m≤n⇒m≤1+n; ≤-refl)
open import Data.Fin using (Fin; fromℕ; fold; toℕ; _ℕ-_) renaming (zero to fzero; suc to fsuc; inject₁ to finject₁)
open import Data.Product
-- open import Data.Tree.Backedges
open import Data.Empty using () renaming (⊥ to Zero)
open import Function using (_∘_; flip)
open import MuCalc.DeBruijn.Base renaming (unfold to unfold')
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.Isomorphism
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (Star)
open import Relation.Nullary

----------------
-- Data Types --
----------------

-- Vectors of fixpoint formulas, with the extra trick that the number of
-- free variables allowed depends on its position in the vector
data Scope (At : Set) : ℕ → Set where
  [] : Scope At zero
  _-,_ : ∀ {n} → (Γ₀ : Scope At n) → (ϕ : μML At n) → {{_ : IsFP ϕ}} → Scope At (suc n)

-- Sublimely-scoped formulas
mutual
  data μMLε {At : Set} {n : ℕ} (Γ : Scope At n) : Set where
    var : (x : Fin n) → μMLε Γ
    μML₀ : (op : Op₀ At) → μMLε Γ
    μML₁ : (op : Op₁) → (ϕ : μMLε Γ) → μMLε Γ
    μML₂ : (op : Op₂) → (ϕ : μMLε Γ) → (ψ : μMLε Γ) → μMLε Γ
    μMLη : (op : Opη) → {ψ : μML At (suc n)} → (ϕ : μMLε (Γ -, μMLη op ψ)) → ψ ≈ ϕ → μMLε Γ

  data _≈_ {At : Set} {n : ℕ} {Γ : Scope At n} : μML At n → μMLε Γ → Set where
    var  : (x : Fin n) → (var x) ≈ (var x)
    μML₀ : (op : Op₀ At) → μML₀ op ≈ μML₀ op
    μML₁ : (op : Op₁)
         → {ϕ : μML At n} {ϕ' : μMLε Γ} → ϕ ≈ ϕ'
         → μML₁ op ϕ ≈ μML₁ op ϕ'
    μML₂ : (op : Op₂)
         → {ϕ : μML At n} {ϕ' : μMLε Γ} {ψ : μML At n} {ψ' : μMLε Γ}
         → ϕ ≈ ϕ' → ψ ≈ ψ'
         → μML₂ op ϕ ψ ≈ μML₂ op ϕ' ψ'
    μMLη : (op : Opη)
         → {ϕ : μML At (suc n)} {ϕ' : μMLε (Γ -, μMLη op ϕ)} → (p : ϕ ≈ ϕ')
         → μMLη op ϕ ≈ μMLη op ϕ' p

data IsFPε {At : Set} : {n : ℕ} {Γ : Scope At n} → μMLε Γ → Set where
  instance fp : ∀ {n} {Γ : Scope At n} {op : Opη} {ψ : μML At (suc n)} {ϕ : μMLε (Γ -, μMLη op ψ)} {p : ψ ≈ ϕ} → IsFPε (μMLη op ϕ p)

pattern ⊤ = μML₀ tt
pattern ⊥ = μML₀ ff
pattern lit x = μML₀ (at x)
pattern ¬lit x = μML₀ (¬at x)
pattern ■ ϕ = μML₁ box ϕ
pattern ◆ ϕ = μML₁ dia ϕ
pattern _∧_ ϕ ψ = μML₂ and ϕ ψ
pattern _∨_ ϕ ψ = μML₂ or ϕ ψ
pattern μ' ϕ p = μMLη mu ϕ p
pattern ν' ϕ p = μMLη nu ϕ p

--------------------------
-- Machinery for Scopes --
--------------------------

-- Lookup has a wrinkle; beacuse the elements of the scope all live at different
-- indices, we have to inject the element we're looking up up to the same level as
-- the head. Otherwise the result index would need to depend on x, and it'd be awful
lookup : ∀ {At n} → (Γ : Scope At n) → (x : Fin n) → μML At n
lookup (Γ -, ϕ) fzero = inject₁ ϕ
lookup (Γ -, ϕ) (fsuc x) = inject₁ (lookup Γ x)

----------------------------
-- Machinery for Formulas --
----------------------------

-- ≈ is prop-valued
≈-irrelevant : ∀ {At n} {Γ : Scope At n} {ϕ : μML At n} {ψ : μMLε Γ} → (p q : ϕ ≈ ψ) → p ≡ q
≈-irrelevant (var x) (var .x) = refl
≈-irrelevant (μML₀ op) (μML₀ .op) = refl
≈-irrelevant (μML₁ op p) (μML₁ .op q) = cong (μML₁ op) (≈-irrelevant p q)
≈-irrelevant (μML₂ op p1 p2) (μML₂ .op q1 q2) = cong₂ (μML₂ op) (≈-irrelevant p1 q1) (≈-irrelevant p2 q2)
≈-irrelevant (μMLη op p) (μMLη .op .p) = refl

cong-fp : ∀ {op At n} {Γ : Scope At n}
        → {ϕ' ψ' : μML At (suc n)}
        → {ϕ : μMLε (Γ -, μMLη op ϕ')} {ψ : μMLε (Γ -, μMLη op ψ')}
        → (eq : ψ' ≡ ϕ')
        → ϕ ≡ subst (λ z → μMLε (Γ -, μMLη op z)) eq ψ -- Please let me live to not regret this
        → {p : ϕ' ≈ ϕ} {q : ψ' ≈ ψ}
        → (μMLη op ϕ p) ≡ (μMLη op ψ q)
cong-fp {op = op} {ϕ = ϕ} refl refl = cong (μMLη op ϕ) (≈-irrelevant _ _)

-- We can downwardly traverse a formula and annotate it with the scope infomation as long
-- as we have an annotated scope for everything "above" it in the sf tree.
recompute-scope : ∀ {At : Set} {n : ℕ} → (Γ : Scope At n) → μML At n → μMLε Γ
recompute-scope-eq : ∀ {At : Set} {n : ℕ} → (Γ : Scope At n) → (ϕ : μML At n) → ϕ ≈ recompute-scope Γ ϕ

recompute-scope Γ (var x) = var x
recompute-scope Γ (μML₀ op) = μML₀ op
recompute-scope Γ (μML₁ op ϕ) = μML₁ op (recompute-scope Γ ϕ)
recompute-scope Γ (μML₂ op ϕ ψ) = μML₂ op (recompute-scope Γ ϕ) (recompute-scope Γ ψ)
recompute-scope Γ (μMLη op ϕ) = μMLη op (recompute-scope (Γ -, μMLη op ϕ) ϕ) (recompute-scope-eq (Γ -, μMLη op ϕ) ϕ)

recompute-scope-eq Γ (var x) = var x
recompute-scope-eq Γ (μML₀ op) = μML₀ op
recompute-scope-eq Γ (μML₁ op ϕ) = μML₁ op (recompute-scope-eq Γ ϕ)
recompute-scope-eq Γ (μML₂ op ϕ ψ) = μML₂ op (recompute-scope-eq Γ ϕ) (recompute-scope-eq Γ ψ)
recompute-scope-eq Γ (μMLη op ϕ) = μMLη op (recompute-scope-eq (Γ -, μMLη op ϕ) ϕ)

-- And of course, we can throw our richer scope away.
forget-scope : ∀ {At : Set} {n : ℕ} {Γ : Scope At n} → μMLε Γ → μML At n
forget-scope (var x) = var x
forget-scope (μML₀ op) = μML₀ op
forget-scope (μML₁ op ϕ) = μML₁ op (forget-scope ϕ)
forget-scope (μML₂ op ϕ ψ) = μML₂ op (forget-scope ϕ) (forget-scope ψ)
forget-scope (μMLη op ϕ p) = μMLη op (forget-scope ϕ)

-- ψ≈ϕ tells us that ψ and ϕ are the same term, only that ψ is well-scoped and ϕ is sublimely-scoped.
-- So if we forget the scope of ϕ, they should agree on the nose.
≈⇒≡∘forget : ∀ {At n} {Γ : Scope At n}
      → {ψ : μML At n} {ϕ : μMLε Γ}
      → (p : ψ ≈ ϕ)
      → forget-scope ϕ ≡ ψ
≈⇒≡∘forget (var x) = refl
≈⇒≡∘forget (μML₀ op) = refl
≈⇒≡∘forget (μML₁ op p) = cong (μML₁ op) (≈⇒≡∘forget p)
≈⇒≡∘forget (μML₂ op p q) = cong₂ (μML₂ op) (≈⇒≡∘forget p) (≈⇒≡∘forget q)
≈⇒≡∘forget (μMLη op p) = cong (μMLη op) (≈⇒≡∘forget p)

-- This one isn't needed for the iso, but is still useful.
forget-scope-eq : ∀ {At : Set} {n : ℕ} {Γ : Scope At n} → (ϕ : μMLε Γ) → forget-scope ϕ ≈ ϕ
forget-scope-eq (var x) = var x
forget-scope-eq (μML₀ op) = μML₀ op
forget-scope-eq (μML₁ op ϕ) = μML₁ op (forget-scope-eq ϕ)
forget-scope-eq (μML₂ op ϕ ψ) = μML₂ op (forget-scope-eq ϕ) (forget-scope-eq ψ)
forget-scope-eq (μMLη op {ψ} ϕ p) = subst (_≈ μMLη op ϕ p) (cong (μMLη op) (sym (≈⇒≡∘forget p))) (μMLη op p)


-- Forgetting scope preserves being a fixpoint formula, of course.
forget-scope-fp : ∀ {At : Set} {n : ℕ} {Γ : Scope At n} (ϕ : μMLε Γ) → {{_ : IsFPε ϕ}} → IsFP (forget-scope ϕ)
forget-scope-fp (μMLη op ϕ x) = fp

forget-recompute : ∀ {At n} (Γ : Scope At n) → (ϕ : μML At n) → ϕ ≡ forget-scope (recompute-scope Γ ϕ)
forget-recompute Γ (var x) = refl
forget-recompute Γ (μML₀ op) = refl
forget-recompute Γ (μML₁ op ϕ) = cong (μML₁ op) (forget-recompute Γ ϕ)
forget-recompute Γ (μML₂ op ϕ ψ) = cong₂ (μML₂ op) (forget-recompute Γ ϕ) (forget-recompute Γ ψ)
forget-recompute Γ (μMLη op ϕ) = cong (μMLη op) (forget-recompute (Γ -, μMLη op ϕ) ϕ)


-- this is basically just saying that substing the same element after proving the types equal is the identity,
-- but the weird dependencies seem to make it not an obvious instance of any much more general case.
rf-lemma : ∀ {At} {n} {Γ : Scope At n} {op} {ψ ϕ : μML At (suc n)}
         → (eq : ϕ ≡ ψ)
         → recompute-scope (Γ -, μMLη op ψ) ϕ
         ≡ subst (λ z → μMLε (Γ -, μMLη op z)) eq
           (recompute-scope (Γ -, μMLη op ϕ) ϕ)
rf-lemma refl = refl

recompute-forget : ∀ {At n} (Γ : Scope At n) → (ϕ : μMLε Γ) → ϕ ≡ recompute-scope Γ (forget-scope ϕ)
recompute-forget Γ (var x) = refl
recompute-forget Γ (μML₀ op) = refl
recompute-forget Γ (μML₁ op ϕ) = cong (μML₁ op) (recompute-forget Γ ϕ)
recompute-forget Γ (μML₂ op ϕ ψ) = cong₂ (μML₂ op) (recompute-forget Γ ϕ) (recompute-forget Γ ψ)
recompute-forget {At} {n} Γ (μMLη op {ψ} ϕ p) = cong-fp (≈⇒≡∘forget p) (trans (recompute-forget (Γ -, μMLη op ψ) ϕ) (rf-lemma (≈⇒≡∘forget p)))

-- Open terms are open graphs! In the well-scoped world, the scope only tells us how many backedges were chopped off,
-- so there are many ways to close the term. But with the "sublime" scopes, there is 1* unique way to close the term.
-- *Starting from the outermost μ/ν, at least; we can always put more propositional/modal operators above that.
-- This means that for every choice of scope Γ, we have the following isomorphism:

sublime-iso : {At : Set} {n : ℕ} (Γ : Scope At n) → μML At n ≃ μMLε Γ
to (sublime-iso Γ) = recompute-scope Γ
from (sublime-iso Γ) = forget-scope
from-to (sublime-iso Γ) = forget-recompute Γ
to-from (sublime-iso Γ) = recompute-forget Γ

------------------------------------------------------------------
-- The example family of formulas (prop 10 of the LIPICS paper) --
------------------------------------------------------------------
formulafam-β₀ : (At : Set) (n : ℕ) → μML At n
formulafam-β₀ At n = μMLη mu (fold (μML At) (λ {n = n} ϕ → μML₂ and (var (fromℕ n)) (inject₁ ϕ)) (var fzero) (fromℕ n))


-- formulafam-α : (At : Set) (n : ℕ) (i j : Fin n) → μML At n
-- formulafam-β' : (At : Set) (n : ℕ) → (i : Fin n) → μML At n

-- formulafam-α At n i j = {!!}
-- formulafam-β' At n i = {!!}



------------------
-- Substitution --
------------------

{-
-- In this setting, the coherence proofs required in the fixpoint cases make life harder.
-- We need to prove a fair few extra lemmas as we go, some mutually.
module Sub where
  -- Rescoping
  rescope' : ∀ {At n m} {Γ : Scope At n} {Δ : Scope At m}
          → (Fin n → Fin m) -- if we have an embedding of n to m...
          → μMLε Γ → μMLε Δ -- then we can rescope' n-terms to be m-terms.
  rescope-eq : ∀ {At} {n} {m} {Γ : Scope At n} {Δ : Scope At m}
               (ρ : Fin n → Fin m)
             → {ψ : μML At n} {ϕ : μMLε Γ}
             → ψ ≈ ϕ
             → rescope ρ ψ ≈ rescope' {Γ = Γ} {Δ = Δ} ρ ϕ

  rescope' ρ (var x) = var (ρ x)
  rescope' ρ (μML₀ op) = μML₀ op
  rescope' ρ (μML₁ op ϕ) = μML₁ op (rescope' ρ ϕ)
  rescope' ρ (μML₂ op ϕ ψ) = μML₂ op (rescope' ρ ϕ) (rescope' ρ ψ)
  rescope' ρ (μMLη op {ψ} ϕ p) = μMLη op {rescope (ext ρ) ψ} (rescope' (ext ρ) ϕ) (rescope-eq (ext ρ) p)

  rescope-eq ρ (var x) = var (ρ x)
  rescope-eq ρ (μML₀ op) = μML₀ op
  rescope-eq ρ (μML₁ op p) = μML₁ op (rescope-eq ρ p)
  rescope-eq ρ (μML₂ op p q) = μML₂ op (rescope-eq ρ p) (rescope-eq ρ q)
  rescope-eq ρ (μMLη op p) = μMLη op (rescope-eq (ext ρ) p)

  -- Parallel substitutions are maps from variables to formulae
  Subst' : {At : Set} → ℕ → {m : ℕ} → Scope At m → Set
  Subst' n Γ = Fin n → μMLε Γ

  -- Substitution extension
  exts' : ∀ {At n m} {Δ : Scope At m} {ψ : μML At m} {{_ : IsFP ψ}} → Subst' n Δ → Subst' (suc n) (Δ -, ψ)
  exts' σ fzero = var fzero
  exts' σ (fsuc x) =  rescope' fsuc (σ x)


  -- Rescoping commutes with forgetting the scope.
  rescope-forget : ∀ {At n} {Γ : Scope At n} {ψ : μML At n} {{_ : IsFP ψ}}
                 → (ϕ : μMLε Γ)
                 → rescope fsuc (forget-scope ϕ) ≈ rescope' {Γ = Γ} {Δ = Γ -, ψ} fsuc ϕ
  rescope-forget (var y) = var (fsuc y)
  rescope-forget (μML₀ op) = μML₀ op
  rescope-forget (μML₁ op ϕ) = μML₁ op (rescope-forget ϕ)
  rescope-forget (μML₂ op ϕ ψ) = μML₂ op (rescope-forget ϕ) (rescope-forget ψ)
  rescope-forget {ψ = ψ} (μMLη op {ϕ'} ϕ p) with rescope-forget {ψ = rescope fsuc ψ} {{rescope-preserves-fp ψ}} ϕ
  ... | z = {!_≈_.μMLη op {rescope (ext fsuc) (forget-scope ϕ)} {rescope' (ext fsuc) ϕ} (rescope-eq (ext fsuc) z)  !}

  -- Substitution extension commutes with forgetting the scope.
  -- If we downgrade the substitution to the WS world then extend there, thats the same as extending up here in SS land then downgrading the result.
  exts-forget : ∀ {At n m} {Δ : Scope At m} {ψ : μML At m} {{_ : IsFP ψ}}
              → (σ : Subst' n Δ) → (x : Fin (suc n)) → exts (forget-scope ∘ σ) x ≈ exts' {ψ = ψ} σ x
  exts-forget σ fzero = var fzero
  exts-forget σ (fsuc x) = rescope-forget (σ x)

  -- The above as a real (pointwise) identity.
  exts-forget-comm : ∀ {At n m} {Δ : Scope At m} {ψ : μML At m} {{_ : IsFP ψ}}
                   → (σ : Subst' n Δ) → exts (forget-scope ∘ σ) ≗ (forget-scope ∘ (exts' {ψ = ψ} σ))
  exts-forget-comm σ x = sym (≈⇒≡∘forget (exts-forget σ x))


  -- Executing a parallel substitution
  sub' : ∀ {At n m} {Δ : Scope At n} {Γ : Scope At m} → Subst' n Γ → μMLε Δ → μMLε Γ
  sub-forget-eq : ∀ {At n m} {Γ : Scope At n} {Δ : Scope At m}
                → (σ : Subst' n Δ)
                → {ψ : μML At n} {ϕ : μMLε Γ}
                → ψ ≈ ϕ
                → sub (forget-scope ∘ σ) ψ ≈ sub' σ ϕ

  sub' σ (var x) = σ x
  sub' σ (μML₀ op) = μML₀ op
  sub' σ (μML₁ op ϕ) = μML₁ op (sub' σ ϕ)
  sub' σ (μML₂ op ϕ ψ) = μML₂ op (sub' σ ϕ) (sub' σ ψ)
  sub' σ (μMLη op {ψ} ϕ p) = μMLη op {sub (exts (forget-scope ∘ σ)) ψ} (sub' (exts' σ) ϕ) {!(sub-forget-eq (exts' σ) p)!} -- same problem/solution as goal below I think

  sub-forget-eq σ (var x) = forget-scope-eq (σ x)
  sub-forget-eq σ (μML₀ op) = μML₀ op
  sub-forget-eq σ (μML₁ op p) = μML₁ op (sub-forget-eq σ p)
  sub-forget-eq σ (μML₂ op p q) = μML₂ op (sub-forget-eq σ p) (sub-forget-eq σ q)
  sub-forget-eq σ {μMLη op ϕ} {μMLη op ϕ' p} (μMLη op p) = μMLη op {!subst (λ z → sub z ϕ ≈ sub' (exts' σ) ϕ') ? (sub-forget-eq (exts' σ) p)!} -- do I need to postulate funext here, or is there a way around? there must be a way around, since finext is not needed if going via the iso...

  -- Single substitution is a special case of parallel substitution
  sub₀' : ∀ {At n} {Γ : Scope At n} → μMLε Γ → Subst' (suc n) Γ
  sub₀' ϕ fzero = ϕ -- at 0 we substitute
  sub₀' ϕ (fsuc x) = var x -- elsewhere we leave step the variable

  _[_]' : ∀ {At n} {Γ : Scope At n} {ϕ : μML At n} {{_ : IsFP ϕ}} → μMLε (Γ -, ϕ) → μMLε Γ → μMLε Γ
  _[_]' {n} {At} ϕ δ =  sub' (sub₀' δ) ϕ

-}

-------------------------------
-- Definition of the Closure --
-------------------------------

-- If we were to try to naively replicate the implementation of substitution here, we'd be
-- restricted (specifically in the implementation of subst extension) by how prescriptive our scopes are.
-- (TODO: I'm not 100% convinced this is true; I probably just missed something.)
-- So instead, we just directly use the isomorphism.
unfold : ∀ {At n} {Γ : Scope At n} (ϕ : μMLε Γ) → {{_ : IsFPε ϕ}} → μMLε Γ
unfold {Γ = Γ} ϕ {{isFp}} = recompute-scope Γ (unfold' (forget-scope ϕ) {{forget-scope-fp ϕ}})

-- instad of saying (unfold μϕ), lets try (unfold ϕ) where ϕ has at least 1 free var, and we
-- unfold that outermost var. may be neater
unfoldsf : ∀ {At n} {Γ : Scope At n} {ψ : μML At n} {{_ : IsFP ψ}} → (ϕ : μMLε (Γ -, ψ)) → μMLε Γ
unfoldsf {Γ = Γ} {ψ = ψ} ϕ = recompute-scope Γ ((forget-scope ϕ) [ ψ ])

-- The one-step closure relation.
-- This is the foundation of the correctness criteria for the algorithm.
data _~C~>_ {At : Set} : (ϕ ψ : μMLε {At} []) → Set where
  down  : (op : Op₁) (ϕ : μMLε [])   → μML₁ op ϕ ~C~> ϕ
  left  : (op : Op₂) (ϕ ψ : μMLε []) → μML₂ op ϕ ψ ~C~> ϕ
  right : (op : Op₂) (ϕ ψ : μMLε []) → μML₂ op ϕ ψ ~C~> ψ
  thru  : (ϕ : μMLε []) {{_ : IsFPε ϕ}} → ϕ ~C~> unfold ϕ

-- ϕ is in the closure of ξ if there is a path ξ ~...~> ϕ.
-- That is, the membership relation for the Fischer-Ladner closure set is the transitive reflexive
-- closure of _<~C~_
_∈-Closure_ : {At : Set} → (ϕ ξ : μMLε {At} []) → Set
ϕ ∈-Closure ξ = Star (_~C~>_) ξ ϕ

-- The closure of ϕ is defined as the set of all formulas reachable in this way from ϕ.
Closure : {At : Set} → μMLε {At} [] → Set
Closure {At} ϕ = Σ[ ψ ∈ μMLε [] ] (ψ ∈-Closure ϕ)


---------------------------
-- Computing the Closure --
---------------------------

-- {1,2}-ary trees that store data at both nodes and leaves.
-- Nodes are labelled ■/◆/∧/∨/μ/ν
data Tree (X : Set) : Set where
  lf : X → Tree X
  n1 : Op₁ → X → Tree X → Tree X
  n2 : Op₂ → X → Tree X → Tree X → Tree X
  nη : Opη → X → Tree X → Tree X

data _∈T_ {X : Set} : X → Tree X → Set where
  here₀ : ∀ {x y}           → x ≡ y   → x ∈T lf y
  here₁ : ∀ {op x y t}      → x ≡ y   → x ∈T n1 op y t
  down  : ∀ {op x y t}      → x ∈T t  → x ∈T n1 op y t
  here₂ : ∀ {op x y lt rt}  → x ≡ y   → x ∈T n2 op y lt rt
  left  : ∀ {op x y lt rt}  → x ∈T lt → x ∈T n2 op y lt rt
  right : ∀ {op x y lt rt}  → x ∈T rt → x ∈T n2 op y lt rt
  hereη : ∀ {op x y t}      → x ≡ y   → x ∈T nη op y t
  thru  : ∀ {op x y t}      → x ∈T t  → x ∈T nη op y t

-- The expansion map for well-scoped formulas. Defined at that level first because
-- that's where substitution is easy.
expand : ∀ {n At} → Scope At n → μML At n → μML At 0
expand [] ϕ = ϕ
expand (Γ -, Γ₀) ϕ = expand Γ (ϕ [ Γ₀ ])

-- The expansion map for sublimely-scoped formulas.
expandε : ∀ {At n} {Γ : Scope At n} → μMLε Γ → μMLε {At} []
expandε {Γ = Γ} ϕ = recompute-scope [] (expand Γ (forget-scope ϕ))

-- The closure is the expansion of all the subformulas.
-- NB: There will be duplicates! We need to allow for back and left edges
-- a la Ghani & Hamana to de-deuplicate.
closure : ∀ {At n} {Γ : Scope At n} → (ϕ : μMLε Γ) → Tree (μMLε {At} [])
closure {Γ = Γ} α@(var x) = lf (expandε α)
closure {Γ = Γ} α@(μML₀ op) = lf (expandε α)
closure {At} {Γ = Γ} α@(μML₁ op ϕ) = n1 op (expandε α) (closure ϕ)
closure {At} {Γ = Γ} α@(μML₂ op ϕ ψ) = n2 op (expandε α) (closure ϕ) (closure ψ)
closure {At} {Γ = Γ} α@(μMLη op ϕ p) = nη op (expandε α) (closure ϕ)

-- Some illustrative examples of both types of membership proof
private module _ where
  test1 : _∈-Closure_ {Zero} ⊤ (■ (■ (■ ⊤)))
  test1 =  down box (■ (■ ⊤))
    Star.◅ down box (■ ⊤)
    Star.◅ down box ⊤
    Star.◅ Star.ε

  test2 : ⊤ ∈T closure {Zero} {Γ = []} (■ (■ (■ ⊤)))
  test2 = down (down (down (here₀ refl)))


-----------------
-- Subformulas --
-----------------

-- Context extension. Δ is an extension of Γ if it has Γ as a prefix
data _prefix-of_ {At : Set} {n : ℕ} (Γ : Scope At n) : {m : ℕ} (Δ : Scope At m) → Set where
  ε : {Δ : Scope At n} → Γ ≡ Δ → Γ prefix-of Δ
  cons : ∀ {m : ℕ} {Δ : Scope At m} → (ϕ : μML At m) {{q : IsFP ϕ}} → Γ prefix-of Δ → Γ prefix-of (Δ -, ϕ)

prefix-of-weaken : ∀ {At n m} {Γ : Scope At n} {Δ : Scope At m} {ϕ : μML At n} {{p : IsFP ϕ}}
                 → (Γ -, ϕ) prefix-of Δ → Γ prefix-of Δ
prefix-of-weaken (ε refl) = cons _ (ε refl)
prefix-of-weaken (cons ϕ p) = cons _ (prefix-of-weaken p)

prefix-of-trans : ∀ {At i j k} {Γ : Scope At i} {Δ : Scope At j} {Θ : Scope At k}
                → Γ prefix-of Δ → Δ prefix-of Θ → Γ prefix-of Θ
prefix-of-trans (ε refl) q = q
prefix-of-trans p (ε refl) = p
prefix-of-trans (cons ϕ p) (cons ψ q) = cons ψ (prefix-of-trans (cons ϕ p) q)

-- The direct subformula relation.
-- ξ ⊐ ϕ means ϕ is a subformula of ξ, or equivalently, there is a path ξ ~~> ϕ in the SF tree
data _⊏_ {At : Set} {n m : ℕ} {Γ : Scope At n} {Δ : Scope At m} : (ψ : μMLε Δ) → (ϕ : μMLε Γ) → {{p : Γ prefix-of Δ}} → Set where
  down  : ∀ op {{p : Γ prefix-of Δ}} {ψ : μMLε Δ} {ϕ : μMLε Γ}       → (ψ ⊏ ϕ)  → (ψ ⊏ (μML₁ op ϕ))
  left  : ∀ op {{p : Γ prefix-of Δ}} {ψ : μMLε Δ} {ϕˡ ϕʳ : μMLε Γ}   → (ψ ⊏ ϕˡ) → (ψ ⊏ (μML₂ op ϕˡ ϕʳ))
  right : ∀ op {{p : Γ prefix-of Δ}} {ψ : μMLε Δ} {ϕˡ ϕʳ : μMLε Γ}   → (ψ ⊏ ϕʳ) → (ψ ⊏ (μML₂ op ϕˡ ϕʳ))
  under : ∀ op {ψ : μMLε Δ} {ϕ' : μML At (suc n)} {ϕ : μMLε (Γ -, μMLη op ϕ')} {{p : (Γ -, μMLη op ϕ') prefix-of Δ}}  {q : ϕ' ≈ ϕ} → (ψ ⊏ ϕ) → (ψ ⊏ (μMLη op ϕ q)) {{prefix-of-weaken p}}

data _∈SF_ {At : Set} : {n m : ℕ} {Γ : Scope At n} {Δ : Scope At m} → (ϕ : μMLε Δ) → (ξ : μMLε Γ) → {{p : Γ prefix-of Δ}} → Set where
  ε : ∀ {n} {Γ : Scope At n} {ϕ : μMLε Γ} → (ϕ ∈SF ϕ) {{ε refl}}
  _◅_ : ∀ {i j k} {Γ : Scope At i} {Δ : Scope At j} {Θ : Scope At k} {{p : Γ prefix-of Δ}} {{q : Δ prefix-of Θ}} {ϕ : μMLε Γ} {ψ : μMLε Δ} {ξ : μMLε Θ}
      → (ξ ⊏ ψ) → (ψ ∈SF ϕ) → (ξ ∈SF ϕ) {{prefix-of-trans p q}}

------------------------------------------
-- Correctness of the Closure Algorithm --
------------------------------------------

-- An important lemma; if ϕ ∈ closure ξ, then ϕ ∈ closure (unfold (μ ξ))
closure-unfold : ∀ {At} {op} {ξ' : μML At 1} (ξ : μMLε ([] -, μMLη op ξ')) {x : ξ' ≈ ξ} (ϕ : μMLε [])
               → ϕ ∈T closure ξ → ϕ ∈T closure (unfold (μMLη op ξ x))
closure-unfold (var x) ϕ (here₀ refl) = {!here₀!}
closure-unfold (μML₀ op) ϕ (here₀ refl) = (here₀ refl)
closure-unfold (μML₁ op ξ) ϕ (here₁ refl) = {!here₁!}
closure-unfold (μML₁ op ξ) ϕ (down p) = down {!closure-unfold ξ ϕ p!} -- recursive call doesnt fit. need to generalise!
closure-unfold (μML₂ op ξ ξ₁) ϕ (here₂ refl) = {!here₂!}
closure-unfold (μML₂ op ξ ξ₁) ϕ (left p) = left {!!}
closure-unfold (μML₂ op ξ ξ₁) ϕ (right p) = right {!!}
closure-unfold (μMLη op ξ x) ϕ (hereη refl) = {!!}
closure-unfold (μMLη op ξ x) ϕ (thru p) = thru {!!}


closure-sound : ∀ {At} (ξ ϕ : μMLε {At} [])
                → (ϕ ∈T closure ξ) → (ϕ ∈-Closure ξ)
closure-sound (μML₀ op)   ϕ (here₀ refl)    = Star.ε
closure-sound (μML₁ op ξ) ϕ (here₁ refl)
  rewrite sym (recompute-forget [] ξ)
  = Star.ε
closure-sound (μML₁ op ξ) ϕ (down p)
  = down op ξ Star.◅ closure-sound ξ ϕ p
closure-sound (μML₂ op ξ θ) ϕ (here₂ refl)
  rewrite sym (recompute-forget [] ξ)
  rewrite sym (recompute-forget [] θ)
  = Star.ε
closure-sound (μML₂ op ξ θ) ϕ (left p)
  = left op ξ θ Star.◅ closure-sound ξ ϕ p
closure-sound (μML₂ op ξ θ) ϕ (right p)
  = right op ξ θ Star.◅ closure-sound θ ϕ p
closure-sound (μMLη op {ψ} ξ x) ϕ (hereη refl)
  = subst (_∈-Closure (μMLη op ξ x)) (cong-fp (≈⇒≡∘forget x) (trans (recompute-forget _ ξ) (eq x))) Star.ε where
    eq : ∀ {At} {op} {ψ : μML At 1} {ξ : μMLε ([] -, μMLη op ψ)} (x : ψ ≈ ξ)
       → recompute-scope ([] -, μMLη op ψ) (forget-scope ξ)
       ≡ subst (λ z → μMLε ([] -, μMLη op z)) (≈⇒≡∘forget x) (recompute-scope ([] -, μMLη op (forget-scope ξ)) (forget-scope ξ))
    eq x rewrite (≈⇒≡∘forget x) = refl

closure-sound (μMLη op ξ x) ϕ (thru p)
  = thru (μMLη op ξ x) Star.◅ {! closure-sound (unfold (μMLη op ξ x)) ϕ (closure-unfold ξ ϕ p) !}
  -- termination checker obviously dislikes this. it feels wrong that we're going to all the trouble of having graph-like terms,
  -- yet we still can't keep track of the fact that unfolding = following a back-edge


-- And the other direction
closure-complete : ∀ {At} (ξ ϕ : μMLε {At} [])
                 → (ϕ ∈-Closure ξ) → (ϕ ∈T closure ξ)
closure-complete = {!!}
