-- The obvious way to do well-scoped terms is to index
-- them by a list of variables that are in scope. However,
-- the reordering that can happen during unfolding makes this
-- problematic, and the solution using sorted lists is
-- cumbersome (subst hell).
--
-- Alternative idea: bake in the unfolding to the inductive definition.
-- We would hope for this definition to be isomorphic to the obvious one,
-- while making it much easier to implement and prove properties about
-- the closure.

module MuCalc.Named.UnfoldingAware.Base (At Var : Set) where

open import Data.Nat
open import Data.List
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Maybe
open import Function

data Opη : Set where
  μ : Opη
  ν : Opη

data Op₀ : Set where
  tt : Op₀
  ff : Op₀
  at  : At → Op₀
  ¬at : At → Op₀

data Op₁ : Set where
  □ : Op₁
  ◆ : Op₁

data Op₂ : Set where
  ∧ : Op₂
  ∨ : Op₂

{-
-- Usual well scoped terms
data Tm (Γ : List Var) : Set where
var  : ∀ {x} → x ∈ Γ → Tm Γ
μML₀ : Op₀ → Tm Γ
μML₁ : Op₁ → Tm Γ → Tm Γ
μML₂ : Op₂ → Tm Γ → Tm Γ → Tm Γ
μMLη : Opη → (x : Var) → Tm (x ∷ Γ) → Tm Γ

-- Terms of the form μx.ϕ and νx.ϕ
data FP {Γ : List Var} : Tm Γ → Set where
fp : ∀ {op x} {ϕ : Tm (x ∷ Γ)} → FP (μMLη op x ϕ)
-}

data Tm : ℕ → Set
data Path : ∀ {n} → Tm n → Set

 -- varless terms, indexed by depth
data Tm where
  var  : Tm 0 -- vars don't know who their binders are. we have to enforce some invariants after the fact with a sigma type. namely, that each var is only owned by one mu/nu
  μML₀ : Op₀ → Tm 0
  μML₁ : ∀ {n} → Op₁ → Tm n → Tm (suc n)
  μML₂ : ∀ {n m} → Op₂ → Tm n → Tm m → Tm (suc $ n ⊔ m)
  μMLη : ∀ {n} → Opη → (ϕ : Tm n) → List (Path ϕ) → Tm (suc n) -- binders know where their usage sites are; this is recorded by a list of paths to the variable usages.

-- A path tells you how to traverse the tree *to a variable usage site*
data Path where
  var   : Path var
  μML₁  : ∀ {n} op (ϕ : Tm n) → Path ϕ → Path (μML₁ op ϕ)
  μMLη  : ∀ {n} op (ϕ : Tm n) → (ps : List $ Path ϕ) → Path ϕ → Path (μMLη op ϕ ps)
  left  : ∀ {n m} → (op : Op₂) (ϕ : Tm n) (ψ : Tm m) → Path ϕ → Path (μML₂ op ϕ ψ)
  right : ∀ {n m} → (op : Op₂) (ϕ : Tm n) (ψ : Tm m) → Path ψ → Path (μML₂ op ϕ ψ)


-- Each binder has a list of paths to their variables. But we need the additional
-- invariant that each variable is bound by a unique binder. ie, only one binder has
-- a path to that variable.
-- 1) Translate the AST to a {1,2}-ary tree that stores maybe a Tm at the leaves, initialised
--    to Nothing.
-- 2) Traverse the formula and tree copy in lockstep. When you encounter a binder, traverse
--    its list of paths. For each path, follow the path down the copy, and check the leaf it
--    takes you to;
-- 3) If the leaf is Nothing, set it to Just (the binder that you started from). If the leaf was already Just,
--    then we've visited it before, and hence the invariant has been broken.
-- 4) At the very end, traverse the tree copy once more to check that all leaves have been set to
--    Just. If not, there are variables without binders, which also isn't allowed.

{-
data TempTree : ∀ {n} → Tm n → Set where
  var : Maybe (Σ[ n ∈ ℕ ] Tm n) → TempTree var -- this is where we have to say where the var was bound
  μML₀ : ∀ op → TempTree (μML₀ op) -- 0s store no data
  μML₁ : ∀ {n} op {ϕ : Tm n} → TempTree ϕ → TempTree (μML₁ op ϕ)
  μML₂ : ∀ {n m} op {ϕ : Tm n} {ψ : Tm m} → TempTree ϕ → TempTree ψ → TempTree (μML₂ op ϕ ψ)
  μMLη : ∀ {n} op {ϕ : Tm n} → TempTree ϕ → (ps : List (Path ϕ)) → TempTree (μMLη op ϕ ps)

initialise : ∀ {n} (ϕ : Tm n) → TempTree ϕ
initialise var = var nothing
initialise (μML₀ x) = μML₀ x
initialise (μML₁ x ϕ) = μML₁ x (initialise ϕ)
initialise (μML₂ x ϕ ψ) = μML₂ x (initialise ϕ) (initialise ψ)
initialise (μMLη x ϕ ps) = μMLη x (initialise ϕ) ps

mark-binders : ∀ {n} {ϕ : Tm n} → TempTree ϕ → TempTree ϕ
mark-binders (var (just x)) = {!!} -- at this point, this feels like the wrong way to do things. we need a way to "fail" in a proof-relevant way
mark-binders (var nothing) = {!!}
mark-binders (μML₀ op) = {!!}
mark-binders (μML₁ op x) = {!!}
mark-binders (μML₂ op x x₁) = {!!}
mark-binders (μMLη op x ps) = {!!}
-}
