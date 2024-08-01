module MuCalc.DeBruijn.Base where

open import Data.Nat hiding (_≟_)
open import Data.Fin using (Fin; zero; suc; _≟_) renaming (inject₁ to fin-inject₁)
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Decidable

--------------------------------------------------------------

data Opη : Set where
  mu : Opη
  nu : Opη

data Op₀ (At : Set) : Set where
  tt : Op₀ At
  ff : Op₀ At
  at  : At → Op₀ At
  ¬at : At → Op₀ At

data Op₁ : Set where
  box : Op₁
  dia : Op₁

data Op₂ : Set where
  and : Op₂
  or : Op₂

-- Formulas are parameterised by the list of names in scope.
data μML (At : Set) (n : ℕ) : Set where
  var : Fin n → μML At n
  μML₀ : (op : Op₀ At) → μML At n
  μML₁ : (op : Op₁) → (ϕ : μML At n) → μML At n
  μML₂ : (op : Op₂) → (ϕ : μML At n) → (ψ : μML At n) → μML At n
  μMLη : (op : Opη) → (ϕ : μML At (suc n)) → μML At n

data IsFP {At : Set} : {n : ℕ} (ϕ : μML At n) → Set where
  fp : {n : ℕ} (op : Opη) → (ψ : μML At (suc n)) → IsFP (μMLη op ψ)

record μFP (At : Set) : Set where
  constructor pack
  field
    {ctx} : ℕ
    {tm} : μML At ctx
    pf : IsFP tm
open μFP

-- Some prettier pattern synonyms
pattern ⊤ = μML₀ tt
pattern ⊥ = μML₀ ff
-- pattern at x = μML₀ at x
-- pattern ¬at x = μML₀ ¬at x
pattern ■ ϕ = μML₁ box ϕ
pattern ◆ ϕ = μML₁ dia ϕ
pattern _∧_ ϕ ψ = μML₂ and ϕ ψ
pattern _∨_ ϕ ψ = μML₂ or ϕ ψ
pattern μ ϕ = μMLη mu ϕ
pattern ν ϕ = μMLη nu ϕ


--------------------------------------------------------------

-- Negation is derived by de Morgan substitutions.
¬ : ∀ {At n} → μML At n → μML At n
¬ (var x)        = var x -- is this right?
¬ ⊤ = ⊥
¬ ⊥ = ⊤
¬ (μML₀ (at x)) = μML₀ (¬at x)
¬ (μML₀ (¬at x)) = μML₀ (at x)
¬ (■ ϕ) = ◆ (¬ ϕ)
¬ (◆ ϕ) = ■ (¬ ϕ)
¬ (ϕ ∧ ψ) = (¬ ϕ) ∨ (¬ ψ)
¬ (ϕ ∨ ψ) = (¬ ϕ) ∧ (¬ ψ)
¬ (μ ϕ) = ν (¬ ϕ)
¬ (ν ϕ) = μ (¬ ϕ)

-- Material implication
_⇒_ : ∀ {At n} → μML At n → μML At n → μML At n
ϕ ⇒ ψ = μML₂ or (¬ ϕ) ψ


--------------------------------------------------------------
-- Substitution --

-- Scope extension
ext : ∀ {n m} → (Fin n → Fin m)
    → Fin (suc n) → Fin (suc m)
ext ρ zero = zero
ext ρ (suc x) = suc (ρ x)

-- Rescoping
rescope : ∀ {n m At} → (Fin n → Fin m) -- if we have an embedding of n to m...
        → μML At n → μML At m -- then we can rescope n-terms to be m-terms.
rescope ρ (var x) = var (ρ x)
rescope ρ (μML₀ op) = μML₀ op
rescope ρ (μML₁ op ϕ) = μML₁ op (rescope ρ ϕ)
rescope ρ (μML₂ op ϕ ψ) = μML₂ op (rescope ρ ϕ) (rescope ρ ψ)
rescope ρ (μMLη op ϕ) = μMLη op (rescope (ext ρ) ϕ)

-- Parallel substitutions are maps from variables to formulae
Subst : Set → ℕ → ℕ → Set
Subst At n m = Fin n → μML At m

-- Substitution extension
exts : ∀ {n m At} → Subst At n m → Subst At (suc n) (suc m)
exts σ zero = var zero
exts σ (suc x) = rescope suc (σ x)

-- Executing a parallel substitution
sub : ∀ {n m At} → Subst At n m → μML At n → μML At m
sub σ (var x) = σ x
sub σ (μML₀ op) = μML₀ op
sub σ (μML₁ op ϕ) = μML₁ op (sub σ ϕ)
sub σ (μML₂ op ϕ ψ) = μML₂ op (sub σ ϕ) (sub σ ψ)
sub σ (μMLη op ϕ) = μMLη op (sub (exts σ) ϕ)

-- Single substitution is a special case of parallel substitution
sub₀ : ∀ {At n} → μML At n → Subst At (suc n) n
sub₀ ϕ zero = ϕ -- at 0 we substitute
sub₀ ϕ (suc x) = var x -- elsewhere we leave step the variable

_[_] : ∀ {n At} → μML At (suc n) → μML At n → μML At n
_[_] {n} {At} ϕ σ = sub (sub₀ σ) ϕ

-- And now fixpoint unfolding is a single substitution
unfold : ∀ {At n} {ϕ : μML At n} → IsFP ϕ → μML At n
unfold (fp op ψ) = ψ [ μMLη op ψ ]
