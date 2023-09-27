open import Algebra.Structure.OICM
open import Relation.Unary.Countable
open import Relation.Binary.PropositionalEquality

module MuCalc.Named.Closure
  {At Var : Set}
  {_<A_ : At → At → Set}
  {_<V_ : Var → Var → Set}
  (<A-STO : IsPropStrictTotalOrder _≡_ _<A_)
  (<V-STO : IsPropStrictTotalOrder _≡_ _<V_)
  (At-countable : IsCountable At)
  (Var-countable : IsCountable Var)
  where

open import Data.FreshList.InductiveInductive
open import Free.IdempotentCommutativeMonoid.Base <V-STO
open import Free.IdempotentCommutativeMonoid.Properties <V-STO

open import MuCalc.Named.Base <A-STO <V-STO At-countable Var-countable
open import MuCalc.Named.Dummies <A-STO <V-STO At-countable Var-countable

data Graph-unfoldε : ∀ {Γ} {ψ' : μMLε []}
                     → (ψ : μFPε ψ') -- the original fixpoint formula that we will substitute for occurrences of z
                     → (ϕ : μMLε (insert (binderOfε ψ) Γ)) -- the formula to traverse. It is a proper subformula of ψ, so must have ψ's binder in scope
                     → μMLε Γ
                     → Set
                     where
  -- we define unfolding to be id on dummies.
  uε     : ∀ {Γ} {ψ' : μMLε []} {ψ : μFPε ψ'} {ϕ' : μML []} {ϕ : μFP ϕ'}
         → Graph-unfoldε {Γ} ψ (ε ϕ) (ε ϕ)
  u0     : ∀ {Γ} {ψ' : μMLε []} {ψ : μFPε ψ'} {op}
         → Graph-unfoldε {Γ} ψ (μML₀ op) (μML₀ op)
  u1     : ∀ {Γ} {ψ' : μMLε []} {ψ : μFPε ψ'} {op} {ϕ : μMLε (insert (binderOfε ψ) Γ)} {S}
         → Graph-unfoldε {Γ} ψ ϕ S → Graph-unfoldε {Γ} ψ (μML₁ op ϕ) (μML₁ op S)
  u2     : ∀ {Γ} {ψ' : μMLε []} {ψ : μFPε ψ'} {op} {L R : μMLε (insert (binderOfε ψ) Γ)} {S T}
         → Graph-unfoldε {Γ} ψ L S → Graph-unfoldε {Γ} ψ R T → Graph-unfoldε {Γ} ψ (μML₂ op L R) (μML₂ op S T)
  -- The interesting cases - var and μ/ν.
  -- For vars, the var is either the one we're currently unfolding or not.
  -- If yes, then substuitute (inside a ε, so that we don't blow up the size for the closure as agda sees it.)
  uv-eq  : ∀ {Γ op x ψ y y∈Γ}
         → x ≡ y → Graph-unfoldε {Γ} (fp op x ψ) (var y y∈Γ) (ε (fp op x (erase ψ)))
  -- If no, then leave it alone.
  uv-neq : ∀ {Γ op x ψ y y∈Γ}
         → (x≢y : x ≢ y) → Graph-unfoldε {Γ} (fp op x ψ) (var y y∈Γ) (var y (insert∈tail Γ y∈Γ (λ y≡x → x≢y (sym y≡x))))
  -- Going under a binder, we may shadow the variable that we're looking for.
  -- If we do, then we can stop here.
  uη-eq  : ∀ {Γ op x ψ op' y} {ϕ : μMLε (insert y (insert x Γ))}
         → (x≡y : x ≡ y) → Graph-unfoldε {Γ} (fp op x ψ) (μMLη op' y ϕ) (μMLη op' y (subst μMLε (≈L→≡ (insert-idempotent (sym x≡y) Γ) ) ϕ))
  -- If we bind a different variable, then we can continue unfolding.
  uη-neq : ∀ {Γ op x ψ op' y} {ϕ : μMLε (insert y (insert x Γ))} {S}
         → (x≢y : x ≢ y) → Graph-unfoldε {insert y Γ} (fp op x ψ) (subst μMLε (≈L→≡ (insert-comm y x Γ)) ϕ) S
         → Graph-unfoldε {Γ} (fp op x ψ) (μMLη op' y ϕ) (μMLη op' y S)
