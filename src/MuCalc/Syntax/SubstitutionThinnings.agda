{-# OPTIONS --safe #-}
module MuCalc.Syntax.SubstitutionThinnings where

open import Data.Nat
open import Data.Fin as F using (Fin)
open import Data.Product
open import Data.Empty
open import Data.Vec as V using (Vec; []; _∷_)
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

open import Function using (_∘_)

open import MuCalc.Base


-- This file mostly follows PLFA (Wadler, Kokke, and Siek, 2020), with the following
-- excptions:
-- 1) We define substitions in tabulated form (ie as vectors rather than functions)

---------------------------
-- Parallel Substitution --
---------------------------


-- Rescopings are maps of variables
Rescope : ℕ → ℕ → Set
Rescope n m = Fin n → Fin m

-- A substitution is a map `Fin n → μML At m`, morally speaking.
-- We tabulate the function as a vector to avoid dealing with funext.
Subst : Set → ℕ → ℕ → Set
Subst At n m = Vec (μML At m) n

-- Rescoping extension
ext : ∀ {n m} → Rescope n m → Rescope (suc n) (suc m)
ext ρ F.zero = F.zero
ext ρ (F.suc x) = F.suc (ρ x)

-- Executing a rescoping
rescope : ∀ {At n m} → Rescope n m -- if we have an mapping of n vars to m vars...
        → μML At n → μML At m -- then we can rescope n-terms to be m-terms.
rescope ρ (var x) = var (ρ x)
rescope ρ (μML₀ op) = μML₀ op
rescope ρ (μML₁ op ϕ) = μML₁ op (rescope ρ ϕ)
rescope ρ (μML₂ op ϕ ψ) = μML₂ op (rescope ρ ϕ) (rescope ρ ψ)
rescope ρ (μMLη op ϕ) = μMLη op (rescope (ext ρ) ϕ)

-- Substitution extension
exts : ∀ {At n m} → Subst At n m → Subst At (suc n) (suc m)
exts σ = (var F.zero) ∷ V.map (rescope F.suc) σ

-- Executing a parallel substitution
⟪_⟫ : ∀ {At n m} → Subst At n m → μML At n → μML At m
⟪ σ ⟫ (var x) = V.lookup σ x
⟪ σ ⟫ (μML₀ op) = μML₀ op
⟪ σ ⟫ (μML₁ op ϕ) = μML₁ op (⟪ σ ⟫ ϕ)
⟪ σ ⟫ (μML₂ op ϕ ψ) = μML₂ op (⟪ σ ⟫ ϕ) (⟪ σ ⟫ ψ)
⟪ σ ⟫ (μMLη op ϕ) = μMLη op (⟪ exts σ ⟫ ϕ)


-----------------------------------
-- The σ-Algebra of Substitution --
-----------------------------------

-- The identity substitution.
ids : ∀ {At n} → Subst At n n
ids = V.tabulate var

-- The "shift" substitution, which increments all the variables.
↑ : ∀ {At n} → Subst At n (suc n)
↑ = V.tabulate (var ∘ F.suc)

-- Substitution composition
_⨟_ : ∀ {At i j k} → Subst At i j → Subst At j k → Subst At i k
σ ⨟ τ = V.map ⟪ τ ⟫ σ

{-

-- The 4th operation of the algebra is the "cons" substitution, which substitutes the
-- head at zero and the tail elsewhere. Since we're in a tabulated setting, this really
-- is cons for vectors. So rather than introducing a new name, we'll just be using _∷_
_•_ : ∀ {At n m} → μML At m → Subst At n m → Subst At (suc n) m
(ϕ • σ) = ϕ ∷ σ

-}

-----------------------------
-- The σ-Algebra Equations --
-----------------------------

sub-head : ∀ {At n m} → (ϕ : μML At n) (σ : Subst At m n)
         → ⟪ ϕ ∷ σ ⟫ (var F.zero) ≡ ϕ
sub-head _ _ = refl

sub-tail : ∀ {At n m} → (ϕ : μML At n) (σ : Subst At m n)
         → ↑ ⨟ (ϕ ∷ σ) ≡ σ
sub-tail ϕ σ = trans (sym (tabulate-∘ ⟪ ϕ ∷ σ ⟫ (var ∘ F.suc))) (tabulate∘lookup σ)


------------------------------------------------
-- Single Substitution and Fixpoint Unfolding --
------------------------------------------------

-- Single substitution is a special case of parallel substitution
sub₀ : ∀ {At n} → μML At n → Subst At (suc n) n
sub₀ ϕ = ϕ ∷ ids

_[_] : ∀ {At n} → μML At (suc n) → μML At n → μML At n
ϕ [ δ ] = ⟪ sub₀ δ ⟫ ϕ

-- And now fixpoint unfolding is a single substitution
unfold : ∀ {At n} (ϕ : μML At n) → {{_ : IsFP ϕ}} → μML At n
unfold (μMLη op ψ) = ψ [ μMLη op ψ ]
