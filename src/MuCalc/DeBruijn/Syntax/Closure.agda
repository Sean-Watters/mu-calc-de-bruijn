
module MuCalc.DeBruijn.Syntax.Closure where

open import Algebra.Structures.Propositional
open import Data.Nat
open import Data.Fin as F
open import Data.Fin.Properties
open import Data.Vec
open import Data.Vec.Properties
open import Data.Sum
open import Function
open import MuCalc.DeBruijn.Base
open import MuCalc.DeBruijn.Guarded
open import Relation.Binary.PropositionalEquality

mutual
  data Guardedε (At : Set) {n : ℕ} (Γ : Vec ℕ n) : Set where
    var : (x : Fin n) → {{NonZero (lookup Γ x)}} → Guardedε At Γ
    μML₀ : (op : Op₀ At) → Guardedε At Γ
    μML₁ : (op : Op₁) → (ϕ : Guardedε At {n} ones) → Guardedε At Γ
    μML₂ : (op : Op₂) → (ϕ : Guardedε At (inc Γ)) → (ψ : Guardedε At (inc Γ)) → Guardedε At Γ
    μMLη : (op : Opη) → (ϕ : Guardedε At (0 ∷ inc Γ)) → Guardedε At Γ
    ε : {ϕ : Guardedε At Γ} → IsFP ϕ → Guardedε At Γ

  data IsFP {At : Set} {n : ℕ} {Γ : Vec ℕ n} : Guardedε At Γ → Set where
    fp : (op : Opη) (ϕ : Guardedε At (0 ∷ inc Γ)) → IsFP (μMLη op ϕ)

-- these are trivial but really annoying to do manually. ned some "deriving" metaprogram...
postulate _<ε_ : {At : Set} {n : ℕ} {Γ : Vec ℕ n} → (ϕ ψ : Guardedε At Γ) → Set
postulate <ε-STO : (At : Set) {n : ℕ} (Γ : Vec ℕ n) → IsPropStrictTotalOrder {Guardedε At Γ} _≡_ _<ε_

open import Data.FreshList.InductiveInductive
open import Free.IdempotentCommutativeMonoid.Base
open import Free.IdempotentCommutativeMonoid.Properties

lem : ∀ {X : Set} {n m : ℕ} (Γ : Vec X n) (Δ : Vec X m)
    → (x : Fin n)
    → lookup (Γ ++ Δ) (x ↑ˡ m) ≡ lookup Γ x
lem {X} {suc n} {m} (y ∷ Γ) Δ zero = refl
lem {X} {suc n} {m} (y ∷ Γ) Δ (suc x) = lem Γ Δ x

lemma : ∀ {X : Set} {n m k : ℕ} (Γ₀ : Vec X n) (Γ₁ : Vec X k) (Δ : Vec X m)
      → (x : Fin n)
      → lookup (Γ₀ ++ Γ₁) (x ↑ˡ k) ≡ lookup (Γ₀ ++ Δ) (x ↑ˡ m)
lemma Γ₀ Γ₁ Δ x = trans (lem Γ₀ Γ₁ x) (sym $ lem Γ₀ Δ x) 

subε : {At : Set} {n m k : ℕ} {Γ₀ : Vec ℕ n} {Γ₁ : Vec ℕ k} {Δ : Vec ℕ m}
    → (ϕ : Guardedε At (Γ₀ ++ Γ₁))
    → Vec (Guardedε At (Γ₀ ++ Δ)) k
    → Guardedε At (Γ₀ ++ Δ)
subε {n = n} {m} {k} {Γ₀} {Γ₁} {Δ} (var x {{p}}) ψs with F.splitAt n {k} x | inspect (F.splitAt n {k}) x
... | inj₁ x' | [ eq ] = var (x' ↑ˡ m)
  {{subst NonZero {lookup (Γ₀ ++ Γ₁) (x' ↑ˡ k)} {lookup (Γ₀ ++ Δ) (x' ↑ˡ m)}
                  (lemma Γ₀ Γ₁ Δ x')
                  (subst (λ α → NonZero (lookup (Γ₀ ++ Γ₁) α)) ( sym $ splitAt⁻¹-↑ˡ eq) p)}}
... | inj₂ x' | p = lookup ψs x'
subε (μML₀ op) ψs = {!!}
subε (μML₁ op ϕ) ψs = {!!}
subε (μML₂ op ϕ ξ) ψs = {!!}
subε (μMLη op ϕ) ψs = {!!}
subε (ε x) ψs = {!!}

unfoldε : {At : Set} {n : ℕ} {Γ : Vec ℕ n}
        → {ϕ' : Guardedε At Γ} (ϕ : IsFP ϕ')
        → Guardedε At Γ
unfoldε (fp op ϕ) = {!subε ϕ!} -- hmm...see below

-- We would like unfolding to be a simple instance of substitution,
-- but the scopes don't match. ϕ has an extra free variable compared to μϕ.
-- So a representation of syntax with binding where strengthening is free
-- would be good; because while ϕ has an extra free variable, ϕ[0/ψ] does *not*,
-- since we substitute away all its occurrences. So maybe co-de Bruijin is the way.
