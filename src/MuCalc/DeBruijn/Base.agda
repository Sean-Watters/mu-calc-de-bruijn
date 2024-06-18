open import Algebra.Structures.Propositional
open import Relation.Binary.PropositionalEquality

module MuCalc.DeBruijn.Base where

open import Data.Nat hiding (_≟_)
open import Data.Fin using (Fin; zero; suc; _≟_) renaming (inject₁ to fin-inject₁)
open import Relation.Binary.PropositionalEquality
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

-- Injection
-- Taking some formula and making it live in a bigger scope
inject₁ : ∀ {At n} → μML At n → μML At (suc n)
inject₁ (var x) = var (fin-inject₁ x)
inject₁ (μML₀ op) = μML₀ op
inject₁ (μML₁ op ϕ) = μML₁ op (inject₁ ϕ)
inject₁ (μML₂ op ϕ ψ) = μML₂ op (inject₁ ϕ) (inject₁ ψ)
inject₁ (μMLη op ϕ) = μMLη op (inject₁ ϕ)

-- Substitution: sub ϕ x ψ  =  ϕ[x\ψ]
-- I feel like a stronger version of this should be possible where the
-- formula being subbed in can be allowed a scope of n+k if all the free
-- vars to replace are under at least k many binders. But that sounds hard

-- ES: Alternatively, I think something like thinnings may be a nice
-- approach for substitution
--
-- Fred: Should have some notions of semantic substitution, so that substitution commutes with taking the semantics.
-- Should make life easier.
sub : ∀ {At n} → μML At n → (m : Fin n) → μML At n → μML At n
sub (var x) y α with x ≟ y
... | yes p = α
... | no ¬p = var x
sub (μML₀ op) _ _ = μML₀ op
sub (μML₁ op ϕ) x α = μML₁ op (sub ϕ x α)
sub (μML₂ op ϕ ψ) x α = μML₂ op (sub ϕ x α) (sub ψ x α)
sub (μMLη op ϕ) x α = μMLη op (sub ϕ (suc x) (inject₁ α))
