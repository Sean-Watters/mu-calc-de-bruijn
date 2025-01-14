module MuCalc.DeBruijn.ExpansionMap where

open import Function

open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin as F using (Fin) renaming (_ℕ-ℕ_ to _-_)
open import Data.Sum
open import Relation.Binary.PropositionalEquality


open import MuCalc.DeBruijn.Base

-- A presentation of formulas that splits the context in half; a fixed k, and
-- the usual n that increments with each binder. k represents an "inaccessible"
-- prefix of the scope containing variables that we don't want to forget about
-- while `n` changes as we traverse.
-- This makes it easier to work with the expansion map (as defined by induction)
-- on formuals; otherwise we end up needing to index formulas by (n + b), and
-- run into the usual green slime troubles.
data μML' (At : Set) (k : ℕ) (n : ℕ) : Set where
  var   : Fin k ⊎ Fin n → μML' At k n
  μML₀  : (op : Op₀ At) → μML' At k n
  μML₁  : (op : Op₁) → (ϕ : μML' At k n) → μML' At k n
  μML₂  : (op : Op₂) → (ϕ : μML' At k n) → (ψ : μML' At k n) → μML' At k n
  μMLη  : (op : Opη) → (ϕ : μML' At k (suc n)) → μML' At k n

-- This function exists to demonstrate the relationship to +, but as the name suggests,
-- actually using it would be a bad smell.
to-slime : ∀ {At n k} → μML' At k n → μML At (k + n)
to-slime (var x) = var (F.join _ _ x)
to-slime (μML₀ op) = μML₀ op
to-slime (μML₁ op ϕ) = μML₁ op (to-slime ϕ)
to-slime (μML₂ op ϕl ϕr) = μML₂ op (to-slime ϕl) (to-slime ϕr)
to-slime {At} {n} {k} (μMLη op ϕ) = μMLη op (subst (μML At) (+-suc k n) (to-slime ϕ))

to-slime-flip : ∀ {At n k} → μML' At k n → μML At (n + k)
to-slime-flip {At} {n} {k} ϕ = subst (μML At) (+-comm k n) (to-slime ϕ)

go : ∀ {i j k l}
    → (Fin i ⊎ Fin j → Fin k ⊎ Fin l)
    → (Fin i ⊎ Fin (suc j) → Fin k ⊎ Fin (suc l))
go f (inj₁ x) = map id F.suc (f (inj₁ x))
go f (inj₂ F.zero) = inj₂ F.zero
go f (inj₂ (F.suc y)) = map id F.suc (f (inj₂ y))

rescope' : ∀ {At i j k l} → (Fin i ⊎ Fin j → Fin k ⊎ Fin l)
         → μML' At i j → μML' At k l
rescope' ρ (var x) = var (ρ x)
rescope' ρ (μML₀ op) = μML₀ op
rescope' ρ (μML₁ op ϕ) = μML₁ op (rescope' ρ ϕ)
rescope' ρ (μML₂ op ϕ ψ) = μML₂ op (rescope' ρ ϕ) (rescope' ρ ψ)
rescope' ρ (μMLη op ϕ) = μMLη op (rescope' (go ρ) ϕ)

injectR : ∀ {At n k} → μML At n → μML' At k n
injectR (var x) = var (inj₂ x)
injectR (μML₀ op) = μML₀ op
injectR (μML₁ op ϕ) = μML₁ op (injectR ϕ)
injectR (μML₂ op ϕl ϕr) = μML₂ op (injectR ϕl) (injectR ϕr)
injectR (μMLη op ϕ) = μMLη op (injectR ϕ)

shiftSplitR : ∀ {n k} → Fin (suc n) ⊎ Fin k  → Fin n ⊎ Fin (suc k)
shiftSplitR {n} {k} x = F.splitAt n (subst Fin (sym $ +-suc n k) (F.join (suc n) k x))

shiftSplitL : ∀ {n k} → Fin k ⊎ Fin (suc n)  → Fin (suc k) ⊎ Fin n
shiftSplitL {n} {k} x = swap (shiftSplitR (swap x))

injectL : ∀ {At n k} → μML At n → μML' At n k
injectL (var x) = var (inj₁ x)
injectL (μML₀ op) = μML₀ op
injectL (μML₁ op ϕ) = μML₁ op (injectL ϕ)
injectL (μML₂ op ϕl ϕr) = μML₂ op (injectL ϕl) (injectL ϕr)
injectL (μMLη op ϕ) = μMLη op (rescope' shiftSplitR (injectL ϕ))

-----------------------
-- The Expansion Map --
-----------------------

-- The expansion map, the way we wish we could have it.
{-
expand : ∀ {At n} → Scope At n → μML At n → μML At 0
expand [] ϕ = ϕ
expand (ϕ ,- Γ) ϕ = expand Γ (ϕ [ Γ₀ ])
-}

-- The expansion map, defined by induction on the formula.
-- More painful to define, easier to prove with (because everything else is by induction on formulas).
-- `n` tells us how many free variables we started with (and are going to instantiate),
-- `b` tracks how many binders we've traversed past, so we know to leave their variables alone.
expand' : ∀ {At n b} → Scope At n → μML' At n b → μML At b
expand-var : ∀ {At n b} → (Γ : Scope At n) → (x : Fin n ⊎ Fin b) → μML At b

expand' Γ (μML₀ op) = μML₀ op
expand' Γ (μML₁ op ϕ) = μML₁ op (expand' Γ ϕ)
expand' Γ (μML₂ op ϕl ϕr) = μML₂ op (expand' Γ ϕl) (expand' Γ ϕr)
expand' {At} {n} Γ (μMLη op ϕ) = μMLη op (expand' Γ ϕ)
expand' {n = n} Γ (var x) = expand-var Γ x

-- For the free var case, we would like to have:
-- `expand Γ b (var x) = expand (unwind Γ x) b (lookup Γ x)`
-- (up to some massaging of indices), but the termination checker won't allow it.
-- So instead we inline the definitions. We could do it in a single top-level definition
-- using `with F.splitAt b x`, but this makes proofs tricky. So we also unroll the `with`
-- into a mutual definition.
expand-var Γ (inj₂ x) = var x -- bound vars are left alone
expand-var {n = suc n} {b} (ϕ ,- Γ) (inj₁ F.zero) = expand' Γ (injectL ϕ) -- free var; lookup and expand
expand-var (ϕ ,- Γ) (inj₁ (F.suc x)) = expand-var Γ (inj₁ x)


expand : ∀ {At n} → Scope At n → μML At n → μML At 0
expand Γ ϕ = expand' Γ (injectL ϕ)


-----------------------------
-- Properties of Expansion --
-----------------------------

-- We can prove that we actually did inline `lookup` and `unwind` just now
expand-lookup : ∀ {At n b} (Γ : Scope At n) (x : Fin n)
              → expand-var {b = b} Γ (inj₁ x) ≡ expand' {n = n - (F.suc x)} {b = b} (unwind Γ x) (injectL (lookup Γ x))
expand-lookup (ϕ ,- Γ) F.zero = refl
expand-lookup (ϕ ,- Γ) (F.suc x) = expand-lookup Γ x

-- Up to reindexing, the original defining equations are now provable. In particular, the first - expansion is identity for sentences.
expand-empty : ∀ {At b} → (ϕ : μML' At 0 b) → expand' [] ϕ ≡ to-slime ϕ
expand-empty (var (inj₂ y)) = refl
expand-empty (μML₀ op) = refl
expand-empty (μML₁ op ϕ) = cong (μML₁ op) (expand-empty ϕ)
expand-empty (μML₂ op ϕl ϕr) = cong₂ (μML₂ op) (expand-empty ϕl) (expand-empty ϕr)
expand-empty (μMLη op ϕ) = cong (μMLη op) (expand-empty ϕ)

-- -- The unfolding of the expansion is an expansion
-- unfold-expand : ∀ {At n} op (Γ : Scope At n) (ϕ : μML' At n 1) → unfold (μMLη op (expand' Γ ϕ)) ≡ expand' (to-slime-flip (μMLη op ϕ) ,- Γ) (rescope' shiftSplitL ϕ)
-- unfold-expand = {!!}
