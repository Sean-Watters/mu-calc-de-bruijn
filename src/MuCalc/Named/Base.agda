open import Algebra.Structure.OICM
open import Relation.Unary.Countable
open import Relation.Binary.PropositionalEquality

module MuCalc.Named.Base
  {At Var : Set}
  {_<A_ : At → At → Set}
  {_<V_ : Var → Var → Set}
  (<A-STO : IsPropStrictTotalOrder _≡_ _<A_)
  (<V-STO : IsPropStrictTotalOrder _≡_ _<V_)
  (At-countable : IsCountable At)
  (Var-countable : IsCountable Var)
  where

open import Data.FreshList.InductiveInductive
open WithIrr _<V_ ( IsPropStrictTotalOrder.<-prop <V-STO )
open import Free.IdempotentCommutativeMonoid.Base <V-STO
open import Free.IdempotentCommutativeMonoid.Properties <V-STO

≈L→≡ : { xs ys : SortedList } -> xs ≈L ys -> xs ≡ ys
≈L→≡ [] = refl
≈L→≡ {cons x xs fx} {cons .x ys fy} (cons refl p) = cons-cong refl (≈L→≡ p)

data Opη : Set where
  μ : Opη
  ν : Opη

data Op₀ : Set where
  ⊤ : Op₀
  ⊥ : Op₀
  at  : At → Op₀
  ¬at : At → Op₀

data Op₁ : Set where
  □ : Op₁
  ◆ : Op₁

data Op₂ : Set where
  ∧ : Op₂
  ∨ : Op₂

-- Formulas are parameterised by the list of names in scope.
data μML (Γ : SortedList) : Set where
  var : (x : Var) → (x∈Γ : x ∈ Γ) → μML Γ
  μML₀ : (op : Op₀) → μML Γ
  μML₁ : (op : Op₁) → (ϕ : μML Γ) → μML Γ
  μML₂ : (op : Op₂) → (ϕ : μML Γ) → (ψ : μML Γ) → μML Γ
  μMLη : (op : Opη) → (x : Var) → (ϕ : μML (insert x Γ)) → μML Γ

-- Views
data μFP : ∀ {Γ} → μML Γ → Set where
  fp : ∀ {Γ} op x → (ϕ : μML (insert x Γ)) → μFP {Γ} (μMLη op x ϕ)

binderOf : ∀ {Γ} {ϕ : μML Γ} → μFP ϕ → Var
binderOf (fp op x ϕ) = x
