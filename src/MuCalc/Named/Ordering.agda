open import Algebra.Structures.Propositional
open import Relation.Unary.Countable
open import Relation.Binary.PropositionalEquality

module MuCalc.Named.Ordering
  {At Var : Set}
  {_<A_ : At → At → Set}
  {_<V_ : Var → Var → Set}
  (<A-STO : IsPropStrictTotalOrder _≡_ _<A_)
  (<V-STO : IsPropStrictTotalOrder _≡_ _<V_)
  (At-countable : IsCountable At)
  (Var-countable : IsCountable Var)
  where

open import Level
open import Data.Product
open import Data.Empty renaming (⊥ to ⊥-type)


open import Function
open import Relation.Nullary
open import Relation.Binary

open import Data.FreshList.InductiveInductive
open import Free.IdempotentCommutativeMonoid.Base <V-STO
open import Free.IdempotentCommutativeMonoid.Properties <V-STO

open import MuCalc.Named.Base <A-STO <V-STO At-countable Var-countable
open import MuCalc.Named.Contexts <A-STO <V-STO At-countable Var-countable

--------------
-- Ordering --
--------------

-- Need a propositional strict total order on formulas so that we can have
-- sorted lists (ie, "sets") of them.
-- Two structurally equal formulas with different gammas are considered equal.

-- The details of this are painful and in a sane universe would be handled automatically.

data _<0_ : Op₀ -> Op₀ -> Set where
  at<at  : ∀ {x y} -> x <A y -> (at x) <0 (at y)
  ¬at<¬at : ∀ {x y} -> x <A y -> (¬at x) <0 (¬at y)

  ⊤<⊥ : ⊤ <0 ⊥
  ⊤<at : ∀ x -> ⊤ <0 (at x)
  ⊤<¬at : ∀ x -> ⊤ <0 (¬at x)
  ⊥<at : ∀ x -> ⊥ <0 (at x)
  ⊥<¬at : ∀ x -> ⊥ <0 (¬at x)
  at<¬at : ∀ x y -> (at x) <0 (¬at y)

data _<1_ : Op₁ -> Op₁ -> Set where
  □<◆ : □ <1 ◆

data _<2_ : Op₂ -> Op₂ -> Set where
  ∧<∨ : ∧ <2 ∨

data _<η_ : Opη -> Opη -> Set where
  μ<ν : μ <η ν

data _<μ_ {Γ Δ : SortedList} : μML Γ -> μML Δ -> Set where
  -- look at the arity first
  v<0 : ∀ {x p v} -> (var x p) <μ (μML₀ v)
  v<1 : ∀ {x p v ψ} -> (var x p) <μ (μML₁ v ψ)
  v<2 : ∀ {x p v ψ ϕ} -> (var x p) <μ (μML₂ v ψ ϕ)
  v<η : ∀ {x p v y ψ} -> (var x p) <μ (μMLη v y ψ)
  0<1 : ∀ {x y ψ} -> (μML₀ x) <μ (μML₁ y ψ)
  0<2 : ∀ {x y ψ ϕ} -> (μML₀ x) <μ (μML₂ y ψ ϕ)
  0<η : ∀ {x y z ϕ} -> (μML₀ x) <μ (μMLη y z ϕ)
  1<2 : ∀ {x y ψ ϕ ξ} -> (μML₁ x ψ) <μ (μML₂ y ϕ ξ)
  1<η : ∀ {x y z ψ ϕ} -> (μML₁ x ψ) <μ (μMLη y z ϕ)
  2<η : ∀ {x y z ψ ϕ ξ} -> (μML₂ x ψ ϕ) <μ (μMLη y z ξ)

  -- if the arity is the same, then look at the operator
  var : ∀ {x y} {x∈Γ : x ∈ Γ} {y∈Δ : y ∈ Δ} -> x <V y -> (var x x∈Γ) <μ (var y y∈Δ)
  op0 : ∀ {x y} -> x <0 y -> (μML₀ x) <μ (μML₀ y)
  op1 : ∀ {x y} {ψ : μML Γ} {ϕ : μML Δ} -> x <1 y -> (μML₁ x ψ) <μ (μML₁ y ϕ)
  op2 : ∀ {x y} {ψ ϕ : μML Γ} {ξ χ : μML Δ} -> x <2 y -> (μML₂ x ψ ϕ) <μ (μML₂ y ξ χ)
  opη : ∀ {x y v w} {ψ : μML (insert v Γ)} {ϕ : μML (insert w Δ)} -> x <η y -> (μMLη x v ψ) <μ (μMLη y w ϕ)

  -- if the fixpoint operators are the same, then look at the bound variable
  varη : ∀ {x y v w} {ψ : μML (insert v Γ)} {ϕ : μML (insert w Δ)} -> x ≡ y -> v <V w -> (μMLη x v ψ) <μ (μMLη y w ϕ)

  -- if the operator is the same, then look at the subformula
  sf1 : ∀ {x y} {ψ : μML Γ} {ϕ : μML Δ} -> x ≡ y -> (ψ) <μ (ϕ) -> (μML₁ x ψ) <μ (μML₁ y ϕ)
  sf2l : ∀ {x y} {ψ ϕ : μML Γ} {ξ χ : μML Δ} -> x ≡ y -> (ψ) <μ (ξ) -> (μML₂ x ψ ϕ) <μ (μML₂ y ξ χ)
  sfη : ∀ {x y v w} {ψ : μML (insert v Γ)} {ϕ : μML (insert w Δ)} -> x ≡ y -> v ≡ w -> (ψ) <μ (ϕ) -> (μMLη x v ψ) <μ (μMLη y w ϕ)

  -- for ∧ and ∨, if the left subformulas are the same, look at the right
  sf2r : ∀ {x y} {ψ ϕ : μML Γ} {ξ χ : μML Δ} -> x ≡ y -> (ψ) ≈ (ξ) -> (ϕ) <μ (χ) -> (μML₂ x ψ ϕ) <μ (μML₂ y ξ χ)


<Γr : ∀ {Γ Δ θ} {ψ : μML Γ} {ϕ : μML Δ} {ξ : μML θ} -> (ψ) <μ (ϕ) -> (ϕ) ≈ (ξ) -> (ψ) <μ (ξ)
<Γr (op0 x) (μML₀ refl) = op0 x
<Γr 0<1 (μML₁ refl y) = 0<1
<Γr (op1 x) (μML₁ refl y) = op1 x
<Γr (sf1 refl x) (μML₁ refl y) = sf1 refl (<Γr x y)
<Γr 0<2 (μML₂ refl y z) = 0<2
<Γr 1<2 (μML₂ refl y z) = 1<2
<Γr (op2 x) (μML₂ refl y z) = op2 x
<Γr (sf2l refl x) (μML₂ refl y z) = sf2l refl (<Γr x y)
<Γr (sf2r refl x y) (μML₂ refl v w) = sf2r refl (≈-trans x v) (<Γr y w)
<Γr 0<η (μMLη refl refl y) = 0<η
<Γr 1<η (μMLη refl refl y) = 1<η
<Γr 2<η (μMLη refl refl y) = 2<η
<Γr (opη x) (μMLη refl refl y) = opη x
<Γr (varη refl x₁) (μMLη refl refl y) = varη refl x₁
<Γr (sfη refl refl x) (μMLη refl refl y) = sfη refl refl (<Γr x y)
<Γr v<0 (μML₀ x) = v<0
<Γr v<1 (μML₁ x w) = v<1
<Γr v<2 (μML₂ x w w₁) = v<2
<Γr v<η (μMLη x x₁ w) = v<η
<Γr (var x) (var refl) = var x

<Γl : ∀ {Γ Δ θ} {ψ : μML Γ} {ϕ : μML Δ} {ξ : μML θ} -> (ψ) ≈ (ϕ) -> (ϕ) <μ (ξ) -> (ψ) <μ (ξ)
<Γl (μML₀ refl) 0<1 = 0<1
<Γl (μML₀ refl) 0<2 = 0<2
<Γl (μML₀ refl) 0<η = 0<η
<Γl (μML₀ refl) (op0 x) = op0 x
<Γl (μML₁ refl x) 1<2 = 1<2
<Γl (μML₁ refl x) 1<η = 1<η
<Γl (μML₁ refl x) (op1 y) = op1 y
<Γl (μML₁ refl x) (sf1 refl z) = sf1 refl (<Γl x z)
<Γl (μML₂ refl x y) 2<η = 2<η
<Γl (μML₂ refl x y) (op2 z) = op2 z
<Γl (μML₂ refl x y) (sf2l refl z) = sf2l refl (<Γl x z)
<Γl (μML₂ refl x y) (sf2r refl v w) = sf2r refl (≈-trans x v) (<Γl y w)
<Γl (μMLη refl refl x) (opη y) = opη y
<Γl (μMLη refl refl x) (varη refl z) = varη refl z
<Γl (μMLη refl refl x) (sfη refl refl y) = sfη refl refl (<Γl x y)
<Γl (var refl) v<0 = v<0
<Γl (var refl) v<1 = v<1
<Γl (var refl) v<2 = v<2
<Γl (var refl) v<η = v<η
<Γl (var refl) (var x) = var x

<V-trans = IsPropStrictTotalOrder.trans <V-STO
<A-trans = IsPropStrictTotalOrder.trans <A-STO
compareV = IsPropStrictTotalOrder.compare <V-STO
compareA = IsPropStrictTotalOrder.compare <A-STO

<0-trans : ∀ {i j k} -> i <0 j -> j <0 k -> i <0 k
<0-trans (at<at x<y) (at<at y<z) = at<at (<A-trans x<y y<z)
<0-trans (¬at<¬at x<y) (¬at<¬at y<z) = ¬at<¬at (<A-trans x<y y<z)
<0-trans (at<at x) (at<¬at _ y) = at<¬at _ _
<0-trans ⊤<⊥ (⊥<at x) = ⊤<at _
<0-trans ⊤<⊥ (⊥<¬at x) = ⊤<¬at _
<0-trans (⊤<at x) (at<at x₁) = ⊤<at _
<0-trans (⊤<at x) (at<¬at .x y) = ⊤<¬at _
<0-trans (⊤<¬at x) (¬at<¬at x₁) = ⊤<¬at _
<0-trans (⊥<at x) (at<at x₁) = ⊥<at _
<0-trans (⊥<at x) (at<¬at .x y) = ⊥<¬at _
<0-trans (⊥<¬at x) (¬at<¬at x₁) = ⊥<¬at _
<0-trans (at<¬at x y₁) (¬at<¬at x₁) = at<¬at _ _

<μ-trans : ∀ {a b c} {i : μML a} {j : μML b} {k : μML c} -> i <μ j -> j <μ k -> i <μ k
<μ-trans 0<1 1<2 = 0<2
<μ-trans 0<1 1<η = 0<η
<μ-trans 0<1 (op1 x) = 0<1
<μ-trans 0<1 (sf1 x y) = 0<1
<μ-trans 0<2 2<η = 0<η
<μ-trans 0<2 (op2 x) = 0<2
<μ-trans 0<2 (sf2l x y) = 0<2
<μ-trans 0<2 (sf2r x x₁ y) = 0<2
<μ-trans 0<η (opη x) = 0<η
<μ-trans 0<η (varη x x₁) = 0<η
<μ-trans 0<η (sfη x x₁ y) = 0<η
<μ-trans 1<2 2<η = 1<η
<μ-trans 1<2 (op2 x) = 1<2
<μ-trans 1<2 (sf2l x y) = 1<2
<μ-trans 1<2 (sf2r x x₁ y) = 1<2
<μ-trans 1<η (opη x) = 1<η
<μ-trans 1<η (varη x x₁) = 1<η
<μ-trans 1<η (sfη x x₁ y) = 1<η
<μ-trans 2<η (opη x) = 2<η
<μ-trans 2<η (varη x x₁) = 2<η
<μ-trans 2<η (sfη x x₁ y) = 2<η
<μ-trans (op0 x) 0<1 = 0<1
<μ-trans (op0 x) 0<2 = 0<2
<μ-trans (op0 x) 0<η = 0<η
<μ-trans (op0 x) (op0 x₁) = op0 (<0-trans x x₁)
<μ-trans (op1 x) 1<2 = 1<2
<μ-trans (op1 x) 1<η = 1<η
<μ-trans (op1 □<◆) (op1 ())
<μ-trans (op1 x) (sf1 refl y) = op1 x
<μ-trans (op2 x) 2<η = 2<η
<μ-trans (op2 ∧<∨) (op2 ())
<μ-trans (op2 x) (sf2l refl y) = op2 x
<μ-trans (op2 x) (sf2r refl x₂ y) = op2 x
<μ-trans (opη μ<ν) (opη ())
<μ-trans (opη x) (varη refl x₂) = opη x
<μ-trans (opη x) (sfη refl refl y) = opη x
<μ-trans (varη refl x₁) (opη x₂) = opη x₂
<μ-trans (varη refl x₁) (varη refl x₃) = varη refl (<V-trans x₁ x₃)
<μ-trans (varη refl x₁) (sfη refl refl y) = varη refl x₁
<μ-trans (sf1 refl x₁) 1<2 = 1<2
<μ-trans (sf1 refl x₁) 1<η = 1<η
<μ-trans (sf1 refl x₁) (op1 x₂) = op1 x₂
<μ-trans (sf1 refl x₁) (sf1 refl y) = sf1 refl (<μ-trans x₁ y)
<μ-trans (sf2l refl x₁) 2<η = 2<η
<μ-trans (sf2l refl x₁) (op2 x₂) = op2 x₂
<μ-trans (sf2l refl x₁) (sf2l refl y) = sf2l refl (<μ-trans x₁ y)
<μ-trans (sf2l refl x₁) (sf2r refl y z) = sf2l refl (<Γr x₁ y)
<μ-trans (sfη refl refl x₂) (opη x₃) = opη x₃
<μ-trans (sfη refl refl x₂) (varη refl x₄) = varη refl x₄
<μ-trans (sfη refl refl x₂) (sfη refl refl y) = sfη refl refl (<μ-trans x₂ y)
<μ-trans (sf2r refl x x₂) 2<η = 2<η
<μ-trans (sf2r refl x x₂) (op2 x₃) = op2 x₃
<μ-trans (sf2r refl x x₂) (sf2l refl y) = sf2l refl (<Γl x y )
<μ-trans (sf2r refl x x₂) (sf2r refl x₄ y) = sf2r refl (≈-trans x x₄) (<μ-trans x₂ y)
<μ-trans v<0 0<1 = v<1
<μ-trans v<0 0<2 = v<2
<μ-trans v<0 0<η = v<η
<μ-trans v<0 (op0 x) = v<0
<μ-trans v<1 1<2 = v<2
<μ-trans v<1 1<η = v<η
<μ-trans v<1 (op1 x) = v<1
<μ-trans v<1 (sf1 x w) = v<1
<μ-trans v<2 2<η = v<η
<μ-trans v<2 (op2 x) = v<2
<μ-trans v<2 (sf2l x w) = v<2
<μ-trans v<2 (sf2r x x₁ w) = v<2
<μ-trans v<η (opη x) = v<η
<μ-trans v<η (varη x x₁) = v<η
<μ-trans v<η (sfη x x₁ w) = v<η
<μ-trans (var x) v<0 = v<0
<μ-trans (var x) v<1 = v<1
<μ-trans (var x) v<2 = v<2
<μ-trans (var x) v<η = v<η
<μ-trans (var x) (var y) = var (<V-trans x y)

compare-Op₀ : Trichotomous _≡_ _<0_
compare-Op₀ ⊤ ⊤ = tri≈ (λ ()) refl (λ ())
compare-Op₀ ⊤ ⊥ = tri< ⊤<⊥ (λ ()) λ ()
compare-Op₀ ⊤ (at x) = tri< (⊤<at x) (λ ()) λ ()
compare-Op₀ ⊤ (¬at x) = tri< (⊤<¬at x) (λ ()) λ ()
compare-Op₀ ⊥ ⊤ = tri> (λ ()) (λ ()) ⊤<⊥
compare-Op₀ ⊥ ⊥ = tri≈ (λ ()) refl λ ()
compare-Op₀ ⊥ (at x) = tri< (⊥<at x) (λ ()) λ ()
compare-Op₀ ⊥ (¬at x) = tri< (⊥<¬at x) (λ ()) λ ()
compare-Op₀ (at x) ⊤ = tri> (λ ()) (λ ()) (⊤<at x)
compare-Op₀ (at x) ⊥ = tri> (λ ()) (λ ()) (⊥<at x)
compare-Op₀ (at x) (at y) with compareA x y
... | tri< a ¬b ¬c = tri< (at<at a) (λ { refl → ¬c a }) λ { (at<at x) → ¬c x }
... | tri≈ ¬a refl ¬c = tri≈ (λ { (at<at x) → ¬c x }) refl λ { (at<at x) → ¬c x }
... | tri> ¬a ¬b c = tri> (λ { (at<at x) → ¬a x }) (λ { refl → ¬b refl }) (at<at c)
compare-Op₀ (at x) (¬at x₁) = tri< (at<¬at x x₁) (λ ()) λ ()
compare-Op₀ (¬at x) ⊤ = tri> (λ ()) (λ ()) (⊤<¬at x)
compare-Op₀ (¬at x) ⊥ = tri> (λ ()) (λ ()) (⊥<¬at x)
compare-Op₀ (¬at x) (at x₁) = tri> (λ ()) (λ ()) (at<¬at x₁ x)
compare-Op₀ (¬at x) (¬at y) with compareA x y
... | tri< a ¬b ¬c = tri< (¬at<¬at a) (λ { refl → ¬c a }) λ { (¬at<¬at x) → ¬c x }
... | tri≈ ¬a refl ¬c = tri≈ (λ { (¬at<¬at x) → ¬c x }) refl λ { (¬at<¬at x) → ¬c x }
... | tri> ¬a ¬b c = tri> (λ { (¬at<¬at x) → ¬a x }) (λ { refl → ¬b refl }) (¬at<¬at c)

compare-Op₁ : Trichotomous _≡_ _<1_
compare-Op₁ □ □ = tri≈ (λ ()) refl (λ ())
compare-Op₁ ◆ ◆ = tri≈ (λ ()) refl (λ ())
compare-Op₁ □ ◆ = tri< □<◆ (λ ()) (λ ())
compare-Op₁ ◆ □ = tri> (λ ()) (λ ()) □<◆

compare-Op₂ : Trichotomous _≡_ _<2_
compare-Op₂ ∧ ∧ = tri≈ (λ ()) refl (λ ())
compare-Op₂ ∨ ∨ = tri≈ (λ ()) refl (λ ())
compare-Op₂ ∧ ∨ = tri< ∧<∨ (λ ()) (λ ())
compare-Op₂ ∨ ∧ = tri> (λ ()) (λ ()) ∧<∨

compare-Opη : Trichotomous _≡_ _<η_
compare-Opη μ μ = tri≈ (λ ()) refl (λ ())
compare-Opη ν ν = tri≈ (λ ()) refl (λ ())
compare-Opη μ ν = tri< μ<ν (λ ()) (λ ())
compare-Opη ν μ = tri> (λ ()) (λ ()) μ<ν

compare-μML : {Γ Δ : SortedList} → (x : μML Γ) (y : μML Δ) → Tri (x <μ y) (x ≈ y) (y <μ x)
compare-μML (μML₀ x) (μML₁ x₁ y) = tri< 0<1 (λ ()) (λ ())
compare-μML (μML₀ x) (μML₂ x₁ y y₁) = tri< 0<2 (λ ()) (λ ())
compare-μML (μML₀ x) (μMLη x₁ x₂ y) = tri< 0<η (λ ()) (λ ())
compare-μML (μML₁ x x₁) (μML₀ x₂) = tri> (λ ()) (λ ()) 0<1
compare-μML (μML₁ x x₁) (μML₂ x₂ y y₁) = tri< 1<2 (λ ()) (λ ())
compare-μML (μML₁ x x₁) (μMLη x₂ x₃ y) = tri< 1<η (λ ()) (λ ())
compare-μML (μML₂ x x₁ x₂) (μML₀ x₃) = tri> (λ ()) (λ ()) 0<2
compare-μML (μML₂ x x₁ x₂) (μML₁ x₃ y) = tri> (λ ()) (λ ()) 1<2
compare-μML (μML₂ x x₁ x₂) (μMLη x₃ x₄ y) = tri< 2<η (λ ()) (λ ())
compare-μML (μMLη x x₁ x₂) (μML₀ x₃) = tri> (λ ()) (λ ()) 0<η
compare-μML (μMLη x x₁ x₂) (μML₁ x₃ y) = tri> (λ ()) (λ ()) 1<η
compare-μML (μMLη x x₁ x₂) (μML₂ x₃ y y₁) = tri> (λ ()) (λ ()) 2<η
compare-μML (var x x₁) (μML₀ x₂) = tri< v<0 (λ ()) (λ ())
compare-μML (var x x₁) (μML₁ x₂ w) = tri< v<1 (λ ()) (λ ())
compare-μML (var x x₁) (μML₂ x₂ w w₁) = tri< v<2 (λ ()) (λ ())
compare-μML (var x x₁) (μMLη x₂ x₃ w) = tri< v<η (λ ()) (λ ())
compare-μML (μML₀ x) (var x₁ x₂) = tri> (λ ()) (λ ()) v<0
compare-μML (μML₁ x v) (var x₁ x₂) = tri> (λ ()) (λ ()) v<1
compare-μML (μML₂ x v v₁) (var x₁ x₂) = tri> (λ ()) (λ ()) v<2
compare-μML (μMLη x x₁ v) (var x₂ x₃) = tri> (λ ()) (λ ()) v<η
compare-μML (μML₀ x) (μML₀ y) with compare-Op₀ x y
... | tri< a ¬b ¬c = tri< (op0 a) (λ { (μML₀ x) → ¬b x}) λ { (op0 x) → ¬c x }
... | tri≈ ¬a b ¬c = tri≈ (λ { (op0 x) → ¬a x}) (μML₀ b) λ { (op0 x) → ¬c x }
... | tri> ¬a ¬b c = tri> (λ { (op0 x) → ¬a x }) (λ { (μML₀ x) → ¬b x }) (op0 c)
compare-μML (μML₁ x ψ) (μML₁ y ϕ) with compare-Op₁ x y
... | tri< a ¬b ¬c = tri< (op1 a) (λ { (μML₁ x v) → ¬b x }) λ { (op1 x) → ¬c x ; (sf1 x v) → ¬b (sym x) }
... | tri> ¬a ¬b c = tri> (λ { (op1 x) → ¬a x ; (sf1 x v) → ¬b x }) (λ { (μML₁ x v) → ¬b x}) (op1 c)
... | tri≈ ¬a b ¬c with compare-μML (ψ) (ϕ)
... | tri< a ¬b ¬c' = tri< (sf1 b a) (λ { (μML₁ x v) → ¬b v }) λ { (op1 x) → ¬c x ; (sf1 x v) → ¬c' v }
... | tri≈ ¬a' b' ¬c' = tri≈ (λ { (op1 x) → ¬a x ; (sf1 x v) → ¬a' v }) (μML₁ b b') λ { (op1 x) → ¬c x ; (sf1 x v) → ¬c' v }
... | tri> ¬a' ¬b c = tri> (λ { (op1 x) → ¬a x ; (sf1 x v) → ¬a' v }) (λ { (μML₁ x v) → ¬b v  }) (sf1 (sym b) c)
compare-μML (μMLη v x ξ) (μMLη w y χ) with compare-Opη v w
... | tri< a ¬b ¬c = tri< (opη a) (λ { (μMLη x x₁ v) → ¬b x }) λ { (opη x) → ¬c x ; (varη x x₁) → ¬b (sym x) ; (sfη x x₁ x₂) → ¬b (sym x)}
... | tri> ¬a ¬b c = tri> (λ { (opη x) → ¬a x ; (varη x x₁) → ¬b x ; (sfη x x₁ x₂) → ¬b x }) (λ { (μMLη x x₁ v) → ¬b x }) (opη c)
... | tri≈ ¬a b ¬c with compareV x y
... | tri< a ¬b ¬c' = tri< (varη b a) (λ { (μMLη x x₁ v) → ¬b x₁}) λ { (opη x) → ¬c x ; (varη x x₁) → ¬c' x₁ ; (sfη x x₁ x₂) → ¬b (sym x₁) }
... | tri> ¬a' ¬b c = tri> (λ { (opη x) → ¬a x ; (varη x x₁) → ¬a' x₁ ; (sfη x x₁ x₂) → ¬b x₁ }) (λ { (μMLη x x₁ v) → ¬b x₁ }) (varη (sym b) c)
... | tri≈ ¬a' b' ¬c' with compare-μML (ξ) (χ)
... | tri< a' ¬b' ¬c'' = tri< (sfη b b' a') (λ { (μMLη x x₁ v) → ¬b' v }) λ { (opη x) → ¬c x ; (varη x x₁) → ¬c' x₁ ; (sfη x x₁ v) → ¬c'' v }
... | tri≈ ¬a'' b'' ¬c'' = tri≈ (λ { (opη x) → ¬a x ; (varη x x₁) → ¬a' x₁ ; (sfη x x₁ v) → ¬a'' v }) (μMLη b b' b'') λ { (opη x) → ¬c x ; (varη x x₁) → ¬c' x₁ ; (sfη x x₁ v) → ¬c'' v }
... | tri> ¬a'' ¬b' c' = tri> (λ { (opη x) → ¬a x ; (varη x x₁) → ¬a' x₁ ; (sfη x x₁ v) → ¬a'' v }) (λ { (μMLη x x₁ v) → ¬b' v }) (sfη (sym b) (sym b') c')
compare-μML (μML₂ x ψ ξ) (μML₂ y ϕ χ) with compare-Op₂ x y
... | tri< a ¬b ¬c = tri< (op2 a) (λ { (μML₂ x v v₁) → ¬b x }) λ { (op2 x) → ¬c x ; (sf2l x v) → ¬b (sym x) ; (sf2r x x₁ v) → ¬b (sym x)}
... | tri> ¬a ¬b c = tri> (λ { (op2 x) → ¬a x ; (sf2l x v) → ¬b x ; (sf2r x x₁ v) → ¬b x }) (λ { (μML₂ x v v₁) → ¬b x }) (op2 c)
... | tri≈ ¬a refl ¬c with compare-μML (ψ) (ϕ)
... | tri< a ¬b ¬c = tri< (sf2l refl a) (λ { (μML₂ x v v₁) → ¬b v }) λ { (sf2l x v) → ¬c v ; (sf2r x x₁ v) → ¬b (≈-sym x₁) }
... | tri> ¬a ¬b c = tri> (λ { (sf2l x v) → ¬a v ; (sf2r x x₁ v) → ¬b x₁}) (λ { (μML₂ x v v₁) → ¬b v }) (sf2l refl c)
... | tri≈ ¬a ψ≈ϕ ¬c with compare-μML (ξ) (χ)
... | tri< a ¬b ¬c' = tri< (sf2r refl ψ≈ϕ a) (λ { (μML₂ x v v₁) → ¬b v₁ }) λ { (sf2l x v) → ¬c v ; (sf2r x x₁ v) → ¬c' v }
... | tri≈ ¬a' b ¬c' = tri≈ (λ { (sf2l x v) → ¬a v ; (sf2r x x₁ v) → ¬a' v }) (μML₂ refl ψ≈ϕ b) λ { (sf2l x v) → ¬c v ; (sf2r x x₁ v) → ¬c' v }
... | tri> ¬a' ¬b c = tri> (λ { (sf2l x v) → ¬a v ; (sf2r x x₁ v) → ¬a' v }) (λ { (μML₂ x v v₁) → ¬b v₁ }) (sf2r refl (≈-sym ψ≈ϕ) c)
compare-μML (var x x∈Γ) (var y ∈Δ) with compareV x y
... | tri< a ¬b ¬c = tri< (var a) (λ { (var b) → ¬b b}) λ { (var c) → ¬c c }
... | tri≈ ¬a b ¬c = tri≈ (λ { (var a) → ¬a a }) (var b) λ { (var c) → ¬c c }
... | tri> ¬a ¬b c = tri> (λ { (var a) → ¬a a }) (λ { (var b) → ¬b b }) (var c)


compare-wrap-μML : Trichotomous (wrap₂ {X = μML} _≈_) (wrap₂ _<μ_)
compare-wrap-μML x y = compare-μML (proj₂ x) (proj₂ y)

-- <μ-STO : IsStrictTotalOrder (wrap₂ {X = μML} _≈_) (wrap₂ _<μ_)
-- IsEquivalence.refl (IsStrictTotalOrder.isEquivalence <μ-STO) = ≈-refl
-- IsEquivalence.sym (IsStrictTotalOrder.isEquivalence <μ-STO) = ≈-sym
-- IsEquivalence.trans (IsStrictTotalOrder.isEquivalence <μ-STO) = ≈-trans
-- IsStrictTotalOrder.trans <μ-STO = <μ-trans
-- IsStrictTotalOrder.compare <μ-STO = compare-wrap-μML

<0-propositional : ∀ {x y} → (p q : x <0 y) → p ≡ q
<0-propositional (at<at x) (at<at x₁) = cong at<at (IsPropStrictTotalOrder.<-prop <A-STO x x₁)
<0-propositional (¬at<¬at x) (¬at<¬at x₁) = cong ¬at<¬at (IsPropStrictTotalOrder.<-prop <A-STO x x₁)
<0-propositional ⊤<⊥ ⊤<⊥ = refl
<0-propositional (⊤<at x) (⊤<at .x) = refl
<0-propositional (⊤<¬at x) (⊤<¬at .x) = refl
<0-propositional (⊥<at x) (⊥<at .x) = refl
<0-propositional (⊥<¬at x) (⊥<¬at .x) = refl
<0-propositional (at<¬at x y) (at<¬at .x .y) = refl

<1-propositional : ∀ {x y} → (p q : x <1 y) → p ≡ q
<1-propositional □<◆ □<◆ = refl

<2-propositional : ∀ {x y} → (p q : x <2 y) → p ≡ q
<2-propositional ∧<∨ ∧<∨ = refl

<η-propositional : ∀ {x y} → (p q : x <η y) → p ≡ q
<η-propositional μ<ν μ<ν = refl

-- <μ-propositional : {ϕ ψ : wrap μML} → (p q : (wrap₂ _<μ_) ϕ ψ) → p ≡ q
-- <μ-propositional v<0 v<0 = refl
-- <μ-propositional v<1 v<1 = refl
-- <μ-propositional v<2 v<2 = refl
-- <μ-propositional v<η v<η = refl
-- <μ-propositional 0<1 0<1 = refl
-- <μ-propositional 0<2 0<2 = refl
-- <μ-propositional 0<η 0<η = refl
-- <μ-propositional 1<2 1<2 = refl
-- <μ-propositional 1<η 1<η = refl
-- <μ-propositional 2<η 2<η = refl
-- <μ-propositional (var x) (var x₁) = cong var (IsPropStrictTotalOrder.<-prop <V-STO x x₁)
-- <μ-propositional (op0 x) (op0 x₁) = cong op0 (<0-propositional x x₁)
-- <μ-propositional (op1 x) (op1 x₁) = cong op1 (<1-propositional x x₁)
-- <μ-propositional (op1 ()) (sf1 refl q)
-- <μ-propositional (op2 x) (op2 x₁) = cong op2 (<2-propositional x x₁)
-- <μ-propositional (op2 ()) (sf2l refl q)
-- <μ-propositional (op2 ()) (sf2r refl p q)
-- <μ-propositional (opη x) (opη x₁) = cong opη (<η-propositional x x₁)
-- <μ-propositional (opη ()) (varη refl x₂)
-- <μ-propositional (opη ()) (sfη refl p q)
-- <μ-propositional (varη refl x₁) (opη ())
-- <μ-propositional (varη refl x₁) (varη refl x₃) = cong (varη refl) (IsPropStrictTotalOrder.<-prop <V-STO x₁ x₃)
-- <μ-propositional (varη refl p) (sfη refl refl q) = ⊥-elim $ IsPropStrictTotalOrder.irrefl <V-STO refl p
-- <μ-propositional (sf1 refl p) (op1 ())
-- <μ-propositional (sf1 refl p) (sf1 refl q) = cong (sf1 refl) (<μ-propositional p q)
-- <μ-propositional (sf2l refl p) (op2 ())
-- <μ-propositional (sf2l refl p) (sf2l refl q) = cong (sf2l refl) (<μ-propositional p q)
-- <μ-propositional (sf2l refl p) (sf2r refl x q) = ⊥-elim $ IsStrictTotalOrder.irrefl <μ-STO x p
-- <μ-propositional (sfη refl refl p) (opη ())
-- <μ-propositional (sfη refl refl p) (varη refl q) = ⊥-elim $ IsPropStrictTotalOrder.irrefl <V-STO refl q
-- <μ-propositional (sfη refl refl p) (sfη refl refl q) = cong (sfη refl refl) (<μ-propositional p q)
-- <μ-propositional (sf2r refl x₁ p) (op2 ())
-- <μ-propositional (sf2r refl x p) (sf2l refl q) = ⊥-elim $ IsStrictTotalOrder.irrefl <μ-STO x q
-- <μ-propositional (sf2r refl x p) (sf2r refl y q) = cong₂ (sf2r refl) (≈-propositional x y) (<μ-propositional p q)

-- <μ-PSTO : IsPropStrictTotalOrder (wrap₂ {X = μML} _≈_) (wrap₂ _<μ_)
-- IsPropStrictTotalOrder.isSTO <μ-PSTO = <μ-STO
-- IsPropStrictTotalOrder.≈-prop <μ-PSTO = ≈-propositional
-- IsPropStrictTotalOrder.<-prop <μ-PSTO = <μ-propositional

-- <μ₀-PSTO : IsPropStrictTotalOrder (_≈_ {[]} {[]}) (_<μ_ {[]} {[]})
-- IsEquivalence.refl (IsStrictTotalOrder.isEquivalence (IsPropStrictTotalOrder.isSTO <μ₀-PSTO)) = ≈-refl
-- IsEquivalence.sym (IsStrictTotalOrder.isEquivalence (IsPropStrictTotalOrder.isSTO <μ₀-PSTO)) = ≈-sym
-- IsEquivalence.trans (IsStrictTotalOrder.isEquivalence (IsPropStrictTotalOrder.isSTO <μ₀-PSTO)) = ≈-trans
-- IsStrictTotalOrder.trans (IsPropStrictTotalOrder.isSTO <μ₀-PSTO) = <μ-trans
-- IsStrictTotalOrder.compare (IsPropStrictTotalOrder.isSTO <μ₀-PSTO) = compare-μML
-- IsPropStrictTotalOrder.≈-prop <μ₀-PSTO = ≈-propositional
-- IsPropStrictTotalOrder.<-prop <μ₀-PSTO = <μ-propositional

{-
_<FP_ : μFP' -> μFP' -> Set
(Γ , _ , (fp op x ψ)) <FP (Δ , _ , (fp op' y ϕ)) = (Γ , μMLη op x ψ) <μ (Δ , μMLη op' y ϕ)

-- fixpoint formulas are just formulas, so we ought to be able to use the same proofs
<fp→<μ : ∀ {Γ Δ} {ψ : μML Γ} {ϕ : μML Δ} {p : μFP ψ} {q : μFP ϕ}
       ->(Γ , ψ , p) <FP (Δ , ϕ , q) -> (Γ , ψ) <μ (Δ , ϕ)
<fp→<μ {p = fp v x ψ} {q = fp w y ϕ} z = z

<μ→<fp : ∀ {Γ Δ} {ψ : μML Γ} {ϕ : μML Δ} {p : μFP ψ} {q : μFP ϕ}
       -> (Γ , ψ) <μ (Δ , ϕ) -> (Γ , ψ , p) <FP (Δ , ϕ , q)
<μ→<fp {p = fp v x ψ} {q = fp w y ϕ} z = z

≈fp→≈μ : ∀ {Γ Δ} {ψ : μML Γ} {ϕ : μML Δ} {p : μFP ψ} {q : μFP ϕ}
       ->(Γ , ψ , p) ≈FP' (Δ , ϕ , q) -> (Γ , ψ) ≈ (Δ , ϕ)
≈fp→≈μ {p = fp v x ψ} {q = fp w y ϕ} z = z

≈μ→≈fp : ∀ {Γ Δ} {ψ : μML Γ} {ϕ : μML Δ} {p : μFP ψ} {q : μFP ϕ}
       -> (Γ , ψ) ≈ (Δ , ϕ) -> (Γ , ψ , p) ≈FP' (Δ , ϕ , q)
≈μ→≈fp {p = fp v x ψ} {q = fp w y ϕ} z = z

<FP-STO : IsStrictTotalOrder _≈FP'_ _<FP_
IsEquivalence.refl (IsStrictTotalOrder.isEquivalence <FP-STO) = ≈μ→≈fp ≈-refl
IsEquivalence.sym (IsStrictTotalOrder.isEquivalence <FP-STO) x≈y = ≈μ→≈fp (≈-sym (≈fp→≈μ x≈y))
IsEquivalence.trans (IsStrictTotalOrder.isEquivalence <FP-STO) x≈y y≈z = ≈μ→≈fp (≈-trans (≈fp→≈μ x≈y) (≈fp→≈μ y≈z))
IsStrictTotalOrder.trans <FP-STO x<y y<z = <μ→<fp (<μ-trans (<fp→<μ x<y) (<fp→<μ y<z))
IsStrictTotalOrder.compare <FP-STO (Γ , _ , fp v x ψ) (Δ , _ , fp w y ϕ) = compare-μML (Γ , μMLη v x ψ) (Δ , μMLη w y ϕ)

≈fp-refl = IsEquivalence.refl (IsStrictTotalOrder.isEquivalence <FP-STO)
≈fp-sym = IsEquivalence.sym (IsStrictTotalOrder.isEquivalence <FP-STO)
≈fp-trans = IsEquivalence.trans (IsStrictTotalOrder.isEquivalence <FP-STO)

------------------
-- Setting Γ=Δ --
------------------

_<μ'_ : ∀ {Γ} -> μML Γ -> μML Γ -> Set
_<μ'_ {Γ} ψ ϕ = (Γ , ψ) <μ (Γ , ϕ)

<μ'-STO : ∀ {Γ} -> IsStrictTotalOrder (_≈_ {Γ}) _<μ'_
IsEquivalence.refl (IsStrictTotalOrder.isEquivalence <μ'-STO) = ≈-refl
IsEquivalence.sym (IsStrictTotalOrder.isEquivalence <μ'-STO) = ≈-sym
IsEquivalence.trans (IsStrictTotalOrder.isEquivalence <μ'-STO) = ≈-trans
IsStrictTotalOrder.trans <μ'-STO = <μ-trans
IsStrictTotalOrder.compare (<μ'-STO {Γ}) ψ ϕ = compare-μML (Γ , ψ) (Γ , ϕ)

-------------------------------------------------------------------------------
-- Decidable Equality --

-- If two formulas aren't even structurally equal, then they definitely aren't
-- propositionally equal.
≉→≢ : ∀ {Γ Δ} {ψ : μML Γ} {ϕ : μML Δ} -> ¬ (ψ ≈ ϕ) -> (Γ , ψ) ≢ (Δ , ϕ)
≉→≢ x refl = x ≈-refl

_≟μ_ : Decidable {A = μMLΓ} _≡_
(Γ , ψ) ≟μ (Δ , ϕ) with IsStrictTotalOrder._≟_ <μ-STO (Γ , ψ) (Δ , ϕ)
... | no ¬p = no (≉→≢ ¬p)
... | yes p with _≟L_ (IsStrictTotalOrder._≟_ <V-STO) Γ Δ
... | no Γ≢Δ = no λ { refl → Γ≢Δ refl }
... | yes refl = yes (cong _ (≈→≡ p))

------------------
-- Sorted Lists --
------------------

-}

-- import Free.IdempotentCommutativeMonoid as SL
-- module Listμ₀ = SL <μ₀-PSTO -- lists of closed formulas.

-- module ListFP = SL <FP-STO
