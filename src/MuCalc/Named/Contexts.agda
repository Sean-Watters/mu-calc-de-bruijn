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

open import Level
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Function
open import Relation.Nullary
open import Relation.Binary.Structures

open import Data.FreshList.InductiveInductive
open import Free.IdempotentCommutativeMonoid.Base <V-STO renaming (SortedList to SList-Var)
open import Free.IdempotentCommutativeMonoid.Properties <V-STO renaming (insert-comm to insert-comm')

open import MuCalc.Named.Base <A-STO <V-STO At-countable Var-countable

open IsPropStrictTotalOrder <V-STO hiding (trans)

private
  insert-comm : (x y : Var) (Γ : SList-Var)
              → insert x (insert y Γ) ≡ insert y (insert x Γ)
  insert-comm x y Γ = ≈L→≡ (insert-comm' x y Γ)

  -- insert-idempotent : (x : Var) (Γ : SList-Var)
  --                   → insert x (insert x Γ) ≡ insert x Γ
  -- insert-idempotent x Γ = ≈L→≡ (insert-idempotent' refl Γ)

  -- ∈-irrelevant : ∀ {a} {xs : SList-Var} → (p q : a ∈ xs) → p ≡ q
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

---------------
-- Weakening --
---------------

weaken : ∀ {Γ Δ} (ϕ : μML Γ) → Γ ⊆ Δ → μML Δ
weaken (var x x∈Γ) p = var x (p x∈Γ)
weaken (μML₀ op) p = μML₀ op
weaken (μML₁ op ϕ) p = μML₁ op (weaken ϕ p)
weaken (μML₂ op ϕ ψ) p = μML₂ op (weaken ϕ p) (weaken ψ p)
weaken (μMLη op x ϕ) p = μMLη op x (weaken ϕ (insert-preserves-⊆ refl p))

-------------------
-- Strengthening --
-------------------

freevars-lem : ∀ {Γ a x} (ϕ : μML Γ) (fvs : SList-Var) → a ∈ freevars' fvs ϕ → a ≢ x → a ∈ freevars' (insert x fvs) ϕ
freevars-lem {Γ} {a} {x} (var y y∈Γ) fvs a∈fvs a≢x with y ∈? fvs
freevars-lem {Γ} {a} {x} (var y y∈Γ) fvs () a≢x | yes y∈fvs
... | no  y∉fvs with y ∈? insert x fvs
... | no  y∉xfvs = a∈fvs
... | yes y∈xfvs with ∈∪-elim {y} {cons x [] []} {fvs} y∈xfvs
freevars-lem {Γ} {a} {.y} (var y y∈Γ) fvs (here a≡y) a≢y | no y∉fvs | yes y∈xfvs | inj₁ (here refl) = ⊥-elim $ a≢y a≡y
... | inj₂ y∈fvs = ⊥-elim $ y∉fvs y∈fvs
freevars-lem {Γ} {a} {x} (μML₁ op ϕ) fvs p q = freevars-lem ϕ fvs p q
freevars-lem {Γ} {a} {x} (μML₂ op ϕ ψ) fvs p a≢x with ∈∪-elim {a} {freevars' fvs ϕ} {freevars' fvs ψ} p
... | inj₁ a∈fϕ = ∈∪-introˡ {a} {freevars' (insert x fvs) ϕ} (freevars-lem ϕ fvs a∈fϕ a≢x) (freevars' (insert x fvs) ψ)
... | inj₂ a∈fψ = ∈∪-introʳ {a} {freevars' (insert x fvs) ψ} (freevars' (insert x fvs) ϕ) (freevars-lem ψ fvs a∈fψ a≢x)
freevars-lem {Γ} {a} {x} (μMLη op y ϕ) fvs p a≢x = subst (λ u → a ∈ freevars' u ϕ) (insert-comm x y fvs) (freevars-lem {insert y Γ} {a} {x} ϕ (insert y fvs) p a≢x)

⊆-fv-μ : ∀ Γ op x (ϕ : μML (insert x Γ)) → freevars ϕ ⊆ insert x (freevars {Γ} (μMLη op x ϕ))
⊆-fv-μ Γ op x ϕ = indμ {insert x Γ} (λ u → freevars u ⊆ insert x (freevars {Γ} (μMLη op x u)))
  (pv Γ [] op x)
  (p0 Γ [] op x)
  (p1 Γ [] op x)
  (p2 Γ [] op x)
  (pη Γ [] op x)
  ϕ
  where

  pv : ∀ Γ fvs op x a (a∈xΓ : a ∈ insert x Γ)
     → freevars' fvs (var a a∈xΓ) ⊆ (insert x $ freevars' {Γ} fvs (μMLη op x (var a a∈xΓ)))
  pv Γ fvs op x a a∈xΓ p with a ∈? insert x fvs | a ∈? fvs
  ... | no a∉xfvs  | no a∉fvs = ∈insert-introʳ p
  ... | yes a∈xfvs | no a∉fvs with ∈∪-elim {a} {cons x [] []} {fvs} a∈xfvs
  pv Γ fvs op x .x a∈xΓ (here refl) | yes a∈xfvs | no a∉fvs | inj₁ (here refl) = ∈insert-introˡ x []
  ... | inj₂ a∈fvs = ⊥-elim $ a∉fvs a∈fvs

  p0 : ∀ Γ fvs op x op0
     → freevars' {Γ} fvs (μML₀ op0) ⊆ (insert x $ freevars' {Γ} fvs (μMLη op x (μML₀ op0)))
  p0 Γ fvs op x op0 ()

  p1 : ∀ Γ fvs op x {Δ} (eq : Δ ≡ insert x Γ) op1 (ϕ : μML Δ)
     → freevars' fvs (μML₁ op1 (subst μML eq ϕ)) ⊆ (insert x $ freevars' {Γ} fvs (μMLη op x (μML₁ op1 (subst μML eq ϕ))))
  p1 Γ fvs op x refl op1 ϕ {a} p with a ≟ x
  ... | yes refl = ∈insert-introˡ x (freevars' {insert x Γ} (insert x fvs) ϕ)
  ... | no  a≢x  = ∈insert-introʳ (freevars-lem ϕ fvs p a≢x)

  p2 : ∀ Γ fvs op x {Δ} (eq : Δ ≡ insert x Γ) op2 (ϕ ψ : μML Δ)
     → freevars' fvs (μML₂ op2 (subst μML eq ϕ) (subst μML eq ψ)) ⊆ (insert x $ freevars' {Γ} fvs (μMLη op x (μML₂ op2 (subst μML eq ϕ) (subst μML eq ψ))))
  p2 Γ fvs op x refl op2 ϕ ψ {a} p with a ≟ x
  ... | yes refl = ∈insert-introˡ x (freevars' (insert x fvs) ϕ ∪ freevars' (insert x fvs) ψ)
  ... | no  a≢x with ∈∪-elim {a} {freevars' fvs ϕ} {freevars' fvs ψ} p
  ... | inj₁ a∈fϕ = ∈insert-introʳ (∈∪-introˡ {a} {freevars' (insert x fvs) ϕ} (freevars-lem ϕ fvs a∈fϕ a≢x) (freevars' (insert x fvs) ψ))
  ... | inj₂ a∈fψ = ∈insert-introʳ (∈∪-introʳ {a} {freevars' (insert x fvs) ψ} (freevars' (insert x fvs) ϕ) (freevars-lem ψ fvs a∈fψ a≢x))

  pη : ∀ Γ fvs op x {Δ} a (eq : Δ ≡ insert a (insert x Γ)) opη (ϕ : μML Δ)
     → freevars' {insert x Γ} fvs (μMLη opη a (subst μML eq ϕ)) ⊆ (insert x $ freevars' {Γ} fvs (μMLη op x (μMLη opη a (subst μML eq ϕ))))
  pη Γ fvs op x a refl opη ϕ {b} p with b ≟ x
  ... | yes refl = ∈insert-introˡ b (freevars' (insert a (insert b fvs)) ϕ)
  ... | no  b≢x  = ∈insert-introʳ {b} {x} {freevars' (insert a (insert x fvs)) ϕ} (subst (λ u → b ∈ freevars' u ϕ) (insert-comm x a fvs) (freevars-lem ϕ (insert a fvs) p b≢x))


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

-----------------------------------------
-- Equality of Formulas up to Contexts --
-----------------------------------------




-- The above isn't always easy to manipulate, so we also characterise this notion of equality
-- with the following inductive observational equality relation:
data _≈_ : ∀ {Γ Δ} → μML Γ → μML Δ → Set where
  var : ∀ {Γ Δ x y} { p : x ∈ Γ } → { q : y ∈ Δ } → x ≡ y → _≈_ {Γ} {Δ} (var x p) (var y q)
  μML₀ : ∀ {Γ Δ a b} → a ≡ b → _≈_ {Γ} {Δ} (μML₀ a) (μML₀ b)
  μML₁ : ∀ {Γ Δ a b} {ψ : μML Γ} {ψ' : μML Δ} → a ≡ b → ψ ≈ ψ' → (μML₁ a ψ) ≈ (μML₁ b ψ')
  μML₂ : ∀ {Γ Δ a b} {ψ ϕ : μML Γ} {ψ' ϕ' : μML Δ } → a ≡ b → ψ ≈ ψ' → ϕ ≈ ϕ' → (μML₂ a ψ ϕ) ≈ (μML₂ b ψ' ϕ')
  μMLη : ∀ {Γ Δ a b x y} {ψ : μML (insert x Γ)} {ψ' : μML (insert y Δ)} → a ≡ b → x ≡ y → ψ ≈ ψ' → _≈_ {Γ} {Δ} (μMLη a x ψ) (μMLη b y ψ')

-- This can also be characterised as follows:
-- Two formulas are equal modulo contexts if they have the same free variables,
-- and they are equal as formulas after strengthening the contexts to
-- only include those free variables.
-- This is very unpleasant to work with in practice, however.
-- _≈_ : ∀ {Γ Δ} → μML Γ → μML Δ → Set
-- _≈_ {Γ} {Δ} ϕ ψ = Σ[ eq ∈ (freevars ϕ ≡ freevars ψ) ] subst μML eq (normalize-context ϕ) ≡ normalize-context ψ

-- Properties of ≈' - it is an equivalence relation, and isomorphic with ≈

≈-refl : ∀ {Γ} {ψ : μML Γ} → ψ ≈ ψ
≈-refl {Γ} {var x p} = var refl
≈-refl {Γ} {μML₀ op} = μML₀ refl
≈-refl {Γ} {μML₁ op ψ} = μML₁ refl ≈-refl
≈-refl {Γ} {μML₂ op ψ ϕ} = μML₂ refl ≈-refl ≈-refl
≈-refl {Γ} {μMLη op y ψ} = μMLη refl refl ≈-refl

≈-trans : ∀ {Γ Δ Θ} {ψ : μML Γ} {ϕ : μML Δ} {ξ : μML Θ} → ψ ≈ ϕ → ϕ ≈ ξ → ψ ≈ ξ
≈-trans (var refl) (var refl) = var refl
≈-trans (μML₀ refl) (μML₀ refl) = μML₀ refl
≈-trans (μML₁ refl p) (μML₁ refl q) = μML₁ refl (≈-trans p q)
≈-trans (μML₂ refl p p') (μML₂ refl q q') = μML₂ refl (≈-trans p q) (≈-trans p' q')
≈-trans (μMLη refl refl p) (μMLη refl refl q) = μMLη refl refl (≈-trans p q)

≈-sym : ∀ {Γ Δ} {ψ : μML Γ} {ϕ : μML Δ} → ψ ≈ ϕ → ϕ ≈ ψ
≈-sym (var refl) = var refl
≈-sym (μML₀ refl) = μML₀ refl
≈-sym (μML₁ refl p) = μML₁ refl (≈-sym p)
≈-sym (μML₂ refl p q) = μML₂ refl (≈-sym p) (≈-sym q)
≈-sym (μMLη refl refl p) = μMLη refl refl (≈-sym p)

≈-reflexive : ∀ {Γ} {ϕ ψ : μML Γ} → ϕ ≡ ψ → ϕ ≈ ψ
≈-reflexive refl = ≈-refl

≈-refl-subst : ∀ {Γ Δ} (eq : Γ ≡ Δ) (ϕ : μML Γ) → ϕ ≈ subst μML eq ϕ
≈-refl-subst refl p = ≈-refl

strengthen-preserves-≈ : ∀ {Γ Δ} (ϕ : μML Γ) → (p : freevars ϕ ⊆ Δ) → ϕ ≈ strengthen ϕ p
strengthen-preserves-≈ (var x x∈Γ) p = var refl
strengthen-preserves-≈ (μML₀ op) p = μML₀ refl
strengthen-preserves-≈ (μML₁ op ϕ) p = μML₁ refl (strengthen-preserves-≈ ϕ p)
strengthen-preserves-≈ (μML₂ op ϕ ψ) p = μML₂ refl (strengthen-preserves-≈ ϕ (λ a∈fϕ → p (∈∪-introˡ a∈fϕ (freevars ψ)))) (strengthen-preserves-≈ ψ (λ a∈fψ → p (∈∪-introʳ (freevars ϕ) a∈fψ)))
strengthen-preserves-≈ {Γ} {Δ} (μMLη op x ϕ) p = μMLη refl refl (strengthen-preserves-≈ ϕ (⊆-trans (⊆-fv-μ Γ op x ϕ) (insert-preserves-⊆ refl p)))

normalize-preserves-≈ : ∀ {Γ} (ϕ : μML Γ) → ϕ ≈ normalize-context ϕ
normalize-preserves-≈ ϕ = strengthen-preserves-≈ ϕ ⊆-refl

------------------------------------------
-- Wrapping up contexts in a sigma type --
------------------------------------------

-- It's sometimes better to work with a sigma type
-- Σ[ i ∈ I ] (X i), rather than with just the X i.
-- Here's how.

wrap : ∀ {a b} {I : Set a} → (I → Set b) → Set (a ⊔ b)
wrap {I = I} X = Σ[ i ∈ I ] X i

-- In particular, this is good for binary relations over formulas with different indices.
wrap₂ : ∀ {a b} {I : Set a} {X : I → Set b}
  → (∀ {i j : I} → X i → X j → Set (a ⊔ b))
  → (wrap X → wrap X → Set (a ⊔ b))
wrap₂ f x y = f (proj₂ x) (proj₂ y)

_≈'_ : wrap μML → wrap μML → Set
_≈'_ ϕ ψ = proj₂ ϕ ≈ proj₂ ψ

-- Wrapped observational equality is propositional.
-- NB: We are using K here, so the identity type is also propositional.
≈-propositional : ∀ {Γ} {Δ} {ϕ : μML Γ} {ψ : μML Δ} → (p q : (Γ , ϕ) ≈' (Δ , ψ)) → p ≡ q
≈-propositional (var refl) (var refl) = refl
≈-propositional (μML₀ refl) (μML₀ refl) = refl
≈-propositional (μML₁ refl p) (μML₁ refl q) = cong (μML₁ refl) (≈-propositional p q)
≈-propositional (μML₂ refl p p₁) (μML₂ refl q q₁) = cong₂ (μML₂ refl) (≈-propositional p q) (≈-propositional p₁ q₁)
≈-propositional (μMLη refl refl p) (μMLη refl refl q) = cong (μMLη refl refl) (≈-propositional p q)

-- lem : ∀ {Γ Γ'} Δ Δ' (p : Δ ≡ Δ') (ϕ : μML Γ) (ψ : μML Γ')
--     → (f : ∀ {Θ} Λ → μML Θ → μML Λ)
--     → subst μML p (f Δ ϕ) ≡ f Δ' ψ
--     → f Δ ϕ ≈' f Δ' ψ
-- lem Δ .Δ refl ϕ ψ f p = ≈'-reflexive p

-- ≈→≈'-gen : ∀ {Γ Δ} (ϕ : μML Γ) (ψ : μML Δ)
--          → (g : ∀ {Λ} → μML Λ → SList-Var)
--          → (f : ∀ {Λ} → (ξ : μML Λ) → μML (g ξ))
--          → (f-preserves-≈' : ∀ {Λ} → (ξ : μML Λ) → ξ ≈' f ξ)
--          → (p : g ϕ ≡ g ψ)
--          → subst μML p (f ϕ) ≡ f ψ
--          → f ϕ ≈' f ψ
-- ≈→≈'-gen ϕ ψ g f f-preserves-≈' p q = ≈'-trans (≈'-refl-subst p (f ϕ)) (≈'-reflexive q)

-- ≈→≈' : ∀ {Γ Δ} {ϕ : μML Γ} {ψ : μML Δ} → ϕ ≈ ψ → ϕ ≈' ψ
-- ≈→≈' {Γ} {Δ} {ϕ} {ψ} (p , q) = ≈'-trans (≈'-trans (normalize-preserves-≈' ϕ) (≈→≈'-gen ϕ ψ freevars normalize-context normalize-preserves-≈' p q)) (≈'-sym (normalize-preserves-≈' ψ))

-- μML₁-substlem : ∀ {Γ Δ} (p : Γ ≡ Δ) op (ϕ : μML Γ) → subst μML p (μML₁ op ϕ) ≡ μML₁ op (subst μML p ϕ)
-- μML₁-substlem refl op ϕ = refl

-- μML₂-substlem : subst μML (cong₂ _∪_ p q) (μML₂ op ϕ ψ) ≡ μML₂ op ()

-- ≈'→≈ : ∀ {Γ Δ} {ϕ : μML Γ} {ψ : μML Δ} → ϕ ≈' ψ → ϕ ≈ ψ
-- ≈'→≈ (var refl) = refl , refl
-- ≈'→≈ (μML₀ refl) = refl , refl
-- ≈'→≈ {Γ} {Δ} {μML₁ op ϕ} {μML₁ .op ψ} (μML₁ refl p) with ≈'→≈ p
-- ... | (u , v) =  u , trans (μML₁-substlem u op (strengthen ϕ (λ q → ∈-preserves-≈L q ≈L-refl))) (cong (μML₁ op) v)
-- ≈'→≈ {Γ} {Δ} {μML₂ op ϕ ϕ'} {μML₂ .op ψ ψ'} (μML₂ refl p q) with ≈'→≈ p | ≈'→≈ q
-- ... | (u , v) | (u' , v') = (cong₂ _∪_ u u') , {!trans ? (cong₂ (μML₂ op) v ?)!}
-- ≈'→≈ (μMLη refl refl p) = {!!}

-- -- So the same properties are true for ≈.
-- -- We use the isomorphism every time the contexts are different,
-- -- since direct proof in that situation is very hard.

-- ≈-reflexive : ∀ {Γ} {ϕ ψ : μML Γ} → ϕ ≡ ψ → ϕ ≈ ψ
-- ≈-reflexive refl = {!!}

-- ≈-refl : ∀ {Γ} {ϕ : μML Γ} → ϕ ≈ ϕ
-- ≈-refl {Γ} {ϕ} = ≈-reflexive {ϕ = ϕ} refl

-- ≈-sym : ∀ {Γ Δ} {ϕ : μML Γ} {ψ : μML Δ} → ϕ ≈ ψ → ψ ≈ ϕ
-- ≈-sym p = {!!}
