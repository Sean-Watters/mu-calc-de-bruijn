open import Algebra.Structure.OICM
open import Relation.Unary.Countable
open import Relation.Binary.PropositionalEquality

module MuCalc.Named.Contexts
  {At Var : Set}
  {_<A_ : At → At → Set}
  {_<V_ : Var → Var → Set}
  (<A-STO : IsPropStrictTotalOrder _≡_ _<A_)
  (<V-STO : IsPropStrictTotalOrder _≡_ _<V_)
  (At-countable : IsCountable At)
  (Var-countable : IsCountable Var)
  where

open import Data.Sum
open import Data.Product
open import Function
open import Relation.Nullary

open import Data.FreshList.InductiveInductive
open import Free.IdempotentCommutativeMonoid.Base <V-STO renaming (SortedList to SList-Var)
open import Free.IdempotentCommutativeMonoid.Properties <V-STO renaming (insert-comm to insert-comm')

open import MuCalc.Named.Base <A-STO <V-STO At-countable Var-countable

private
  insert-comm : (x y : Var) (Γ : SList-Var)
              -> insert x (insert y Γ) ≡ insert y (insert x Γ)
  insert-comm x y Γ = ≈L→≡ (insert-comm' x y Γ)

  -- insert-idempotent : (x : Var) (Γ : SList-Var)
  --                   -> insert x (insert x Γ) ≡ insert x Γ
  -- insert-idempotent x Γ = ≈L→≡ (insert-idempotent' refl Γ)

  -- ∈-irrelevant : ∀ {a} {xs : SList-Var} -> (p q : a ∈ xs) -> p ≡ q
  -- ∈-irrelevant = ∈-irrelevant' λ { refl refl → refl }

---------------
-- Induction --
---------------

-- The induction principle we want for formulas which doesn't insist
-- on the contexts being *judgementally* equal.
indμ : ∀ {Γ} (P : μML Γ → Set)
     → (∀ x (x∈Γ : x ∈ Γ) → P (var x x∈Γ))
     → (∀ op → P (μML₀ op))
     → (∀ {Δ} (eq : Δ ≡ Γ) op → (ϕ : μML Δ) → P (μML₁ op (subst μML eq ϕ)))
     → (∀ {Δ} (eq : Δ ≡ Γ) op → (ϕ ψ : μML Δ) → P (μML₂ op (subst μML eq ϕ) (subst μML eq ψ)))
     → (∀ {Δ} x (eq : Δ ≡ (insert x Γ)) op → (ϕ : μML Δ) → P (μMLη op x (subst μML eq ϕ)))
     → ((ϕ : μML Γ) → P ϕ)
indμ P pv p0 p1 p2 pη (var x x∈Γ) = pv x x∈Γ
indμ P pv p0 p1 p2 pη (μML₀ op) = p0 op
indμ P pv p0 p1 p2 pη (μML₁ op ϕ) = p1 refl op ϕ
indμ P pv p0 p1 p2 pη (μML₂ op ϕ ψ) = p2 refl op ϕ ψ
indμ P pv p0 p1 p2 pη (μMLη op x ϕ) = pη x refl op ϕ

-----------------------
-- Sets of Variables --
-----------------------

-- Computes the set of variables which appear in a formula.
-- Note that by construction, variables must always be bound
-- somewhere further up. So when called on a sentence (ϕ : μML [])
-- this computes, in particular, the set of *bound* variables.
-- However, when called on some subformula (ϕ : μML Γ) for non empty Γ,
-- this function will also count the (non-atomic) free variables.
vars : ∀ {Γ} → μML Γ → SList-Var
vars (var x x∈Γ) = cons x [] []
vars (μML₀ op) = []
vars (μML₁ op ϕ) = vars ϕ
vars (μML₂ op ϕ ψ) = vars ϕ ∪ vars ψ
vars (μMLη op x ϕ) = vars ϕ

-- We are often interested in the variables appearing in some subformula that
-- were bound outside the scope of the subformula.
-- We refer to these as the free variables. Note; we do not consider atoms to
-- be free variables.
freevars' : ∀ {Γ} → SList-Var → μML Γ → SList-Var
freevars' acc (var x x∈Γ) with x ∈? acc
... | yes p = []           -- if x was bound by a binder that we traversed past, ignore it
... | no ¬p = cons x [] [] -- otherwise, it's free!
freevars' acc (μML₀ op) = []
freevars' acc (μML₁ op ϕ) = freevars' acc ϕ
freevars' acc (μML₂ op ϕ ψ) = freevars' acc ϕ ∪ freevars' acc ψ
freevars' acc (μMLη op x ϕ) = freevars' (insert x acc) ϕ -- x is no longer free from now on

freevars : ∀ {Γ} → μML Γ → SList-Var
freevars = freevars' []

-------------------
-- Strengthening --
-------------------

⊆-fv-μ : ∀ Γ op x (ϕ : μML (insert x Γ)) → freevars ϕ ⊆ insert x (freevars {Γ} (μMLη op x ϕ))
⊆-fv-μ Γ op x ϕ = indμ {insert x Γ} (λ u → freevars u ⊆ insert x (freevars {Γ} (μMLη op x u)))
  (pv Γ [] op x)
  (p0 Γ [] op x)
  (p1 Γ [] op x)
  (p2 Γ [] op x)
  (pη Γ [] op x)
  ϕ
  where

  pv : ∀ Γ fvs op x a (a∈xΓ : a ∈ insert x Γ) → freevars' fvs (var a a∈xΓ) ⊆ (insert x $ freevars' {Γ} fvs (μMLη op x (var a a∈xΓ)))
  pv = {!!}

  p0 : ∀ Γ fvs op x op0 → freevars' {Γ} fvs (μML₀ op0) ⊆ (insert x $ freevars' {Γ} fvs (μMLη op x (μML₀ op0)))
  p0 = {!!}

  p1 : ∀ Γ fvs op x {Δ} (eq : Δ ≡ insert x Γ) op1 (ϕ : μML Δ) → freevars' fvs (μML₁ op1 (subst μML eq ϕ)) ⊆ (insert x $ freevars' {Γ} fvs (μMLη op x (μML₁ op1 (subst μML eq ϕ))))
  p1 = {!!}

  p2 : ∀ Γ fvs op x {Δ} (eq : Δ ≡ insert x Γ) op2 (ϕ ψ : μML Δ) → freevars' fvs (μML₂ op2 (subst μML eq ϕ) (subst μML eq ψ)) ⊆ (insert x $ freevars' {Γ} fvs (μMLη op x (μML₂ op2 (subst μML eq ϕ) (subst μML eq ψ))))
  p2 = {!!}

  pη : ∀ Γ fvs op x {Δ} a (eq : Δ ≡ insert a (insert x Γ)) opη (ϕ : μML Δ) → freevars' {insert x Γ} fvs (μMLη opη a (subst μML eq ϕ)) ⊆ (insert x $ freevars' {Γ} fvs (μMLη op x (μMLη opη a (subst μML eq ϕ))))
  pη = {!!}

-- We can re-index any formula to have any context,
-- so long as the new context contains all the free variables.
strengthen : ∀ {Γ Δ} → (ϕ : μML Γ) → freevars ϕ ⊆ Δ → μML Δ
strengthen (var x x∈Γ) p = var x (p (here refl))
strengthen (μML₀ op) p = μML₀ op
strengthen (μML₁ op ϕ) p = μML₁ op (strengthen ϕ p)
strengthen (μML₂ op ϕ ψ) p = μML₂ op (strengthen ϕ (⊆-trans (∪-upperboundˡ (freevars ϕ) (freevars ψ)) p)) (strengthen ψ (⊆-trans (∪-upperboundʳ (freevars ϕ) (freevars ψ)) p))
strengthen {Γ} {Δ} (μMLη op x ϕ) p = μMLη op x (strengthen ϕ (⊆-trans (⊆-fv-μ Γ op x ϕ) (insert-preserves-⊆ refl p)))

normalize-context : ∀ {Γ} → (ϕ : μML Γ) → μML (freevars ϕ)
normalize-context ϕ = strengthen ϕ ⊆-refl

-- Other equality of formulas up to contexts
_≈_ : ∀ {Γ Δ} → μML Γ → μML Δ → Set
_≈_ {Γ} {Δ} a b = {!!}
