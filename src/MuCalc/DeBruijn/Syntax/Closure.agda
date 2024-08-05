
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
         → {ϕ : μML At n} {ϕ' : μMLε At Γ} {ψ : μML At n} {ψ' : μMLε At Γ}
         → ϕ ≈ ϕ' → ψ ≈ ψ'
         → μML₂ op ϕ ψ ≈ μML₂ op ϕ' ψ'
    μMLη : (op : Opη)
         → {ϕ : μML At (suc n)} {ϕ' : μMLε At (Γ -, fp op ϕ)} → (p : ϕ ≈ ϕ')
         → μMLη op ϕ ≈ μMLη op ϕ' p

data IsFPε {At : Set} : {n : ℕ} {Γ : Scope At n} → μMLε At Γ → Set where
  fp : ∀ {n} {Γ : Scope At n} → (op : Opη) {ψ : μML At (suc n)} (ϕ : μMLε At (Γ -, fp op ψ)) (p : ψ ≈ ϕ) → IsFPε (μMLη op ϕ p)


-- ≈ is prop-valued
≈-irrelevant : ∀ {At n} {Γ : Scope At n} {ϕ : μML At n} {ψ : μMLε At Γ} → (p q : ϕ ≈ ψ) → p ≡ q
≈-irrelevant (var x) (var .x) = refl
≈-irrelevant (μML₀ op) (μML₀ .op) = refl
≈-irrelevant (μML₁ op p) (μML₁ .op q) = cong (μML₁ op) (≈-irrelevant p q)
≈-irrelevant (μML₂ op p1 p2) (μML₂ .op q1 q2) = cong₂ (μML₂ op) (≈-irrelevant p1 q1) (≈-irrelevant p2 q2)
≈-irrelevant (μMLη op p) (μMLη .op .p) = refl

-- The extra dependencies in the scopes make proving equalities on fixpoint formulas especially tricky.
-- In particular, if we can write the type of this lemma, then it's already easy. But making things fit seems
-- to be the hard part. In particular, forcing both ϕ and ψ to depend on definitionally the same θ is a big ask.

-- (Random thought; the issue seems to be that the equalities on the terms are trivial as soon as we know that
-- the identity type-checks in the first place. But writing down the type is the hard part. Heterogenenous eq? Subst? HoTT?)
cong-fp : ∀ {op At n} {Γ : Scope At n}
        → {ϕ' ψ' : μML At (suc n)}
        → {ϕ : μMLε At (Γ -, fp op ϕ')} {ψ : μMLε At (Γ -, fp op ψ')}
        → (eq : ψ' ≡ ϕ')
        → ϕ ≡ subst (λ z → μMLε At (Γ -, fp op z)) eq ψ -- Please let me live to not regret this
        → {p : ϕ' ≈ ϕ} {q : ψ' ≈ ψ}
        → (μMLη op ϕ p) ≡ (μMLη op ψ q)
cong-fp {op = op} {ϕ = ϕ} refl refl = cong (μMLη op ϕ) (≈-irrelevant _ _)

-- We can downwardly traverse a formula and annotate it with the scope infomation as long
-- as we have an annotated scope for everything "above" it in the sf tree.
recompute-scope : ∀ {At : Set} {n : ℕ} → (Γ : Scope At n) → μML At n → μMLε At Γ
recompute-scope-eq : ∀ {At : Set} {n : ℕ} → (Γ : Scope At n) → (ϕ : μML At n) → ϕ ≈ recompute-scope Γ ϕ

recompute-scope Γ (var x) = var x
recompute-scope Γ (μML₀ op) = μML₀ op
recompute-scope Γ (μML₁ op ϕ) = μML₁ op (recompute-scope Γ ϕ)
recompute-scope Γ (μML₂ op ϕ ψ) = μML₂ op (recompute-scope Γ ϕ) (recompute-scope Γ ψ)
recompute-scope Γ (μMLη op ϕ) = μMLη op (recompute-scope (Γ -, fp op ϕ) ϕ) (recompute-scope-eq (Γ -, fp op ϕ) ϕ)

recompute-scope-eq Γ (var x) = var x
recompute-scope-eq Γ (μML₀ op) = μML₀ op
recompute-scope-eq Γ (μML₁ op ϕ) = μML₁ op (recompute-scope-eq Γ ϕ)
recompute-scope-eq Γ (μML₂ op ϕ ψ) = μML₂ op (recompute-scope-eq Γ ϕ) (recompute-scope-eq Γ ψ)
recompute-scope-eq Γ (μMLη op ϕ) = μMLη op (recompute-scope-eq (Γ -, fp op ϕ) ϕ)

-- And of course, we can throw our richer scope away.
forget-scope : ∀ {At : Set} {n : ℕ} {Γ : Scope At n} → μMLε At Γ → μML At n
forget-scope (var x) = var x
forget-scope (μML₀ op) = μML₀ op
forget-scope (μML₁ op ϕ) = μML₁ op (forget-scope ϕ)
forget-scope (μML₂ op ϕ ψ) = μML₂ op (forget-scope ϕ) (forget-scope ψ)
forget-scope (μMLη op ϕ p) = μMLη op (forget-scope ϕ)

-- ψ≈ϕ tells us that ψ and ϕ are the same term, only that ψ is well-scoped and ϕ is sublimely-scoped.
-- So if we forget the scope of ϕ, they should agree on the nose.
≈⇒≡∘forget : ∀ {At n} {Γ : Scope At n}
      → {ψ : μML At n} {ϕ : μMLε At Γ}
      → (p : ψ ≈ ϕ)
      → forget-scope ϕ ≡ ψ
≈⇒≡∘forget (var x) = refl
≈⇒≡∘forget (μML₀ op) = refl
≈⇒≡∘forget (μML₁ op p) = cong (μML₁ op) (≈⇒≡∘forget p)
≈⇒≡∘forget (μML₂ op p q) = cong₂ (μML₂ op) (≈⇒≡∘forget p) (≈⇒≡∘forget q)
≈⇒≡∘forget (μMLη op p) = cong (μMLη op) (≈⇒≡∘forget p)

-- Forgetting scope preserves being a fixpoint formula, of course.
forget-scope-fp : ∀ {At : Set} {n : ℕ} {Γ : Scope At n} {ϕ : μMLε At Γ} → IsFPε ϕ → IsFP (forget-scope ϕ)
forget-scope-fp (fp op (var x) p) = fp op (var x)
forget-scope-fp (fp op (μML₀ op') p) = fp op (μML₀ op')
forget-scope-fp (fp op (μML₁ op' ϕ) p) = fp op (μML₁ op' (forget-scope ϕ))
forget-scope-fp (fp op (μML₂ op' ϕ ψ) p) = fp op (μML₂ op' (forget-scope ϕ) (forget-scope ψ))
forget-scope-fp (fp op (μMLη op' ϕ q) p) = fp op (μMLη op' (forget-scope ϕ))

forget-recompute : ∀ {At n} (Γ : Scope At n) → (ϕ : μML At n) → ϕ ≡ forget-scope (recompute-scope Γ ϕ)
forget-recompute Γ (var x) = refl
forget-recompute Γ (μML₀ op) = refl
forget-recompute Γ (μML₁ op ϕ) = cong (μML₁ op) (forget-recompute Γ ϕ)
forget-recompute Γ (μML₂ op ϕ ψ) = cong₂ (μML₂ op) (forget-recompute Γ ϕ) (forget-recompute Γ ψ)
forget-recompute Γ (μMLη op ϕ) = cong (μMLη op) (forget-recompute (Γ -, fp op ϕ) ϕ)

-- instinct says this should be an instance of some general fact; we're basically saying that substing the same element after proving the types equal is the identity
-- the general thing will definitely be easier to prove, so let's try and nail that down.
rf-lemma : ∀ {At} {n} {Γ : Scope At n} {op} {ψ : μML At (suc n)}
         → {ϕ : μMLε At (Γ -, fp op ψ)} {p : ψ ≈ ϕ}
         → (eq : forget-scope ϕ ≡ ψ)
         → recompute-scope (Γ -, fp op ψ) (forget-scope ϕ)
         ≡ subst (λ z → μMLε At (Γ -, fp op z)) eq
           (recompute-scope (Γ -, fp op (forget-scope ϕ)) (forget-scope ϕ))
rf-lemma eq = {!!}

recompute-forget : ∀ {At n} (Γ : Scope At n) → (ϕ : μMLε At Γ) → ϕ ≡ recompute-scope Γ (forget-scope ϕ)
recompute-forget Γ (var x) = refl
recompute-forget Γ (μML₀ op) = refl
recompute-forget Γ (μML₁ op ϕ) = cong (μML₁ op) (recompute-forget Γ ϕ)
recompute-forget Γ (μML₂ op ϕ ψ) = cong₂ (μML₂ op) (recompute-forget Γ ϕ) (recompute-forget Γ ψ)
recompute-forget {At} {n} Γ (μMLη op {ψ} ϕ p) = cong-fp (≈⇒≡∘forget p) (trans (recompute-forget (Γ -, fp op ψ) ϕ) {!!})

-- Open terms are open graphs! In the well-scoped world, the scope only tells us how many backedges were chopped off,
-- so there are many ways to close the term. But with the "sublime" scopes, there is 1* unique way to close the term.
-- *Starting from the outermost μ/ν, at least; we can always put more propositional/modal operators above that.
-- This means that for every choice of scope Γ, we have the following isomorphism:

sublime-iso : {At : Set} {n : ℕ} (Γ : Scope At n) → μML At n ≃ μMLε At Γ
to (sublime-iso Γ) = recompute-scope Γ
from (sublime-iso Γ) = forget-scope
from-to (sublime-iso Γ) = forget-recompute Γ
to-from (sublime-iso Γ) = recompute-forget Γ

------------------------------------------------------------------
-- The example family of formulas (prop 10 of the LIPICS paper) --
------------------------------------------------------------------
formulafam-β₀ : (At : Set) (n : ℕ) → μML At n
formulafam-β₀ At n = μMLη mu (fold (μML At) (λ {n = n} ϕ → μML₂ and (var (fromℕ n)) (inject₁ ϕ)) (var fzero) (fromℕ n))


formulafam-α : (At : Set) (n : ℕ) (i j : Fin n) → μML At n
formulafam-β' : (At : Set) (n : ℕ) → (i : Fin n) → μML At n

formulafam-α At n i j = {!!}
formulafam-β' At n i = {!!}


-----------------
-- Subformulas --
-----------------

-- The subformula relation; paths through the trees.
-- Todo: change to ⊒ to match the closure graph convention below?
data _⊑_ {At : Set} : {i j : ℕ} → (ψ : μML At i) (ϕ : μML At j) → {{i ≤ j}} → Set where
  here  : ∀ {i} {ψ ϕ : μML At i} → ψ ≡ ϕ → (ψ ⊑ ϕ) {{≤-refl}}
  down  : ∀ op {i j} {p : i ≤ j} {ψ : μML At i} {ϕ : μML At j} → (ψ ⊑ ϕ) {{p}} → (ψ ⊑ (μML₁ op ϕ)) {{p}}
  left  : ∀ op {i j} {p : i ≤ j} {ψ : μML At i} {ϕˡ ϕʳ : μML At j} → (ψ ⊑ ϕˡ) {{p}} → (ψ ⊑ (μML₂ op ϕˡ ϕʳ)) {{p}}
  right : ∀ op {i j} {p : i ≤ j} {ψ : μML At i} {ϕˡ ϕʳ : μML At j} → (ψ ⊑ ϕʳ) {{p}} → (ψ ⊑ (μML₂ op ϕˡ ϕʳ)) {{p}}
  under : ∀ op {i j} {p : i ≤ j} {ψ : μML At i} {ϕ : μML At (suc j)} → (ψ ⊑ ϕ) {{m≤n⇒m≤1+n p}} → (ψ ⊑ (μMLη op ϕ)) {{p}}

---------------------------
-- Unfolding and Closure --
---------------------------

-- If we were to try to naively replicate the implementation of substitution and unfolding here, we'd be
-- restricted (specifically in the implementation of subst extension) by how prescriptive our scopes are.
-- So instead, we just directly use the isomorphism. Which, besides, is neater.
unfold : ∀ {At n} {Γ : Scope At n} {ϕ : μMLε At Γ} → IsFPε ϕ → μMLε At Γ
unfold {Γ = Γ} ϕ = recompute-scope Γ (unfold' (forget-scope-fp ϕ))

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

-- The closure relation.
-- Only defined on closed formulas for now, though an "open closure"
-- notion could be interesting. What sort of compositional structure
-- is there?
-- Anyway, this is our correctness criteria for the algorithm.
data _~C~>_ {At : Set} : (ϕ ψ : μMLε At []) → Set where
  down  : (op : Op₁) (ϕ : μMLε At [])   → μML₁ op ϕ ~C~> ϕ
  left  : (op : Op₂) (ϕ ψ : μMLε At []) → μML₂ op ϕ ψ ~C~> ϕ
  right : (op : Op₂) (ϕ ψ : μMLε At []) → μML₂ op ϕ ψ ~C~> ψ
  thru  : {ϕ' : μMLε At []} (ϕ : IsFPε ϕ') → ϕ' ~C~> unfold ϕ



postulate _<ε_ : {At : Set} {n : ℕ} {Γ : Scope At n} → (ϕ ψ : μMLε At Γ) → Set
postulate <ε-STO : (At : Set) {n : ℕ} {Γ : Scope At n} → IsPropStrictTotalOrder {μMLε At Γ} _≡_ _<ε_
open import Data.FreshList.InductiveInductive
open import Free.IdempotentCommutativeMonoid.Base
open import Free.IdempotentCommutativeMonoid.Properties
