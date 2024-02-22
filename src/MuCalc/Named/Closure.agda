open import Algebra.Structures.Propositional
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

open import Axiom.Extensionality.Propositional

open import Data.Nat renaming (_<_ to _<ℕ_)
open import Data.Nat.Properties
open import Data.Nat.Induction
open import Induction.WellFounded

open import Data.Product
open import Data.Sum
open import Data.Empty
open import Relation.Nullary

open import Data.FreshList.InductiveInductive
open import Free.IdempotentCommutativeMonoid.Base <V-STO
open import Free.IdempotentCommutativeMonoid.Properties <V-STO

open import MuCalc.Named.Base <A-STO <V-STO At-countable Var-countable
open import MuCalc.Named.Dummies <A-STO <V-STO At-countable Var-countable
open import MuCalc.Named.Contexts <A-STO <V-STO At-countable Var-countable

private
  _≈?_ = IsPropStrictTotalOrder._≟_ <V-STO

disjunction-lem : ∀ {A B : Set} → A ⊎ B → ¬ A → B
disjunction-lem (inj₁ a) ¬a = ⊥-elim (¬a a)
disjunction-lem (inj₂ b) ¬a = b

---------------
-- Unfolding --
---------------

-- Let S denote the result of unfolding of a fixpoint formula μx.ϕ.
-- We define the meaning of this to be (Graph-unfoldε μx.ϕ ϕ S).
data Graph-unfoldε : ∀ {Γ} {ψ' : μMLε []}
                     → (ψ : μFPε ψ') -- the original fixpoint formula that we will substitute for occurrences of z
                     → (ϕ : μMLε (insert (binderOfε ψ) Γ)) -- the formula to traverse. It is a proper subformula of ψ, so must have ψ's binder in scope
                     → μMLε Γ -- The result of the unfolding
                     → Set
                     where
  -- we define unfolding to be id on dummies.
  uε     : ∀ {Γ} {ψ' : μMLε []} {ψ : μFPε ψ'} {ϕ' : μMLε []} {ϕ : μFPε ϕ'}
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
         → x ≡ y → Graph-unfoldε {Γ} (fp op x ψ) (var y y∈Γ) (ε (fp op x ψ))
  -- If no, then leave it alone.
  uv-neq : ∀ {Γ op x ψ y y∈Γ}
         → (x≢y : x ≢ y) → Graph-unfoldε {Γ} (fp op x ψ) (var y y∈Γ) (var y (disjunction-lem (∈insert-elim y∈Γ) (≢-sym x≢y)))
  -- Going under a binder, we may shadow the variable that we're looking for.
  -- If we do, then we can stop here.
  uη-eq  : ∀ {Γ op x ψ op' y} {ϕ : μMLε (insert y (insert x Γ))}
         → (x≡y : x ≡ y) → Graph-unfoldε {Γ} (fp op x ψ) (μMLη op' y ϕ) (μMLη op' y (subst μMLε (≈L→≡ (insert-idempotent' y x Γ x≡y)) ϕ))
  -- If we bind a different variable, then we can continue unfolding.
  uη-neq : ∀ {Γ op x ψ op' y} {ϕ : μMLε (insert y (insert x Γ))} {S}
         → (x≢y : x ≢ y) → Graph-unfoldε {insert y Γ} (fp op x ψ) (subst μMLε (≈L→≡ (insert-comm y x Γ)) ϕ) S
         → Graph-unfoldε {Γ} (fp op x ψ) (μMLη op' y ϕ) (μMLη op' y S)

lenε-substlem : ∀ {Γ Δ} (ϕ : μMLε Γ) (P : Γ ≡ Δ) → lenε (subst μMLε P ϕ) ≤ lenε ϕ
lenε-substlem _ refl = ≤-refl

substμ-preserves-len≤ : ∀ {Γ Δ} {ϕ ψ : μMLε Γ} (P Q : Γ ≡ Δ) → lenε ϕ ≤ lenε ψ → lenε (subst μMLε P ϕ) ≤ lenε (subst μMLε Q ψ)
substμ-preserves-len≤ refl refl p = p

-- To prove that the relation is computable, we implement the function in the usual sense.
-- Need to use wellfounded induction because of the subst in the last case. Very annoying
-- that the termination checker can't see through subst.
-- The benefit is that now the algorithm (here) is decoupled from the extensional behaviour
-- (the relation above), so proofs should be easier and hopefully involve less subst-hell.
-- Hopefully.....
-- Otherwise it may have been better to just swap directly from rewrites to substs without this
-- relational stuff.


unfoldε-computable : ∀ {Γ} {ψ' : μMLε []}
                   → (ψ : μFPε ψ')
                   → (ϕ : μMLε (insert (binderOfε ψ) Γ))
                   → {Acc _<ℕ_ (lenε ϕ)}
                   → Σ[ S ∈ μMLε Γ ] Graph-unfoldε ψ ϕ S -- for all ψ and ϕ, there exists some S which is the result of the unfolding.
unfoldε-computable ψ (ε ϕ) {acc rs}
  = ε ϕ ,
    uε
unfoldε-computable ψ (μML₀ op) {acc rs}
  = μML₀ op ,
    u0
unfoldε-computable ψ (μML₁ op ϕ) {acc rs}
  = μML₁ op (proj₁ (unfoldε-computable ψ ϕ {rs (lenε ϕ) (s≤s ≤-refl)})) ,
    u1 (proj₂ (unfoldε-computable ψ ϕ))
unfoldε-computable ψ (μML₂ op L R) {acc rs}
  = μML₂ op (proj₁ (unfoldε-computable ψ L {rs (lenε L) (s≤s (m≤m+n (lenε L) (lenε R)))})) (proj₁ (unfoldε-computable ψ R {rs (lenε R) (s≤s (m≤n+m (lenε R) (lenε L)))})) ,
    u2 (proj₂ (unfoldε-computable ψ L)) (proj₂ (unfoldε-computable ψ R))
unfoldε-computable {Γ} (fp op x ψ) (var y y∈Γ) {acc rs} with x ≈? y
... | yes refl
  = ε (fp op x ψ) ,
    uv-eq refl
... | no x≢y
  = var y (disjunction-lem (∈insert-elim y∈Γ) (≢-sym x≢y)) ,
    uv-neq x≢y
unfoldε-computable {Γ} (fp op x ψ) (μMLη op' y ϕ) {acc rs} with x ≈? y
... | yes refl
 = μMLη op' y (subst μMLε (≈L→≡ (insert-idempotent y y Γ refl)) ϕ) ,
   uη-eq refl
... | no x≢y
 = μMLη op' y (proj₁ (unfoldε-computable (fp op x ψ) (subst μMLε (≈L→≡ (insert-comm y x Γ)) ϕ) {rs (lenε (subst μMLε (≈L→≡ (insert-comm y x Γ)) ϕ)) (s≤s (lenε-substlem ϕ (≈L→≡ (insert-comm y x Γ))))})) ,
   uη-neq x≢y (proj₂ (unfoldε-computable (fp op x ψ) (subst μMLε (≈L→≡ (insert-comm y x Γ)) ϕ)))

module WithFunext (funext : Extensionality _ _) where
  -- Anyway, it's also *really* a function in the sense of being a functional relation.
  -- That is, the result S and the evidence for it being in the image are both unique for a given input.
  -- ******* NB: Proof requires funext! This will not compute! *******
  unfoldε-functional : ∀ {Γ} {ψ' : μMLε []}
                     → (ψ : μFPε ψ') -- the original fixpoint formula that we will substitute for occurrences of z
                     → (ϕ : μMLε (insert (binderOfε ψ) Γ)) -- the formula to traverse. It is a proper subformula of ψ, so must have ψ's binder in scope
                     → (V W : Σ[ S ∈ μMLε Γ ] Graph-unfoldε ψ ϕ S)
                     → V ≡ W
  unfoldε-functional ψ (ε ϕ) (ε .ϕ , uε) (ε .ϕ , uε)
    = refl
  unfoldε-functional ψ (μML₀ op) (μML₀ .op , u0) (μML₀ .op , u0)
    = refl
  unfoldε-functional ψ (μML₁ op ϕ) (μML₁ .op v  , u1 V) (μML₁ .op w , u1 W)
    = cong (λ {(s , gs) → μML₁ op s , u1 gs}) (unfoldε-functional ψ ϕ (v , V) (w , W))
  unfoldε-functional ψ (μML₂ op l r) ((μML₂ .op vl vr) , u2 Vl Vr) (μML₂ .op wl wr , u2 Wl Wr)
    = cong₂ (λ {(s , gs) (t , gt) → μML₂ op s t , u2 gs gt}) (unfoldε-functional ψ l (vl , Vl) (wl , Wl)) (unfoldε-functional ψ r (vr , Vr) (wr , Wr))
  unfoldε-functional (fp op x ψ) .(var _ _) (_ , uv-eq refl) (_ , uv-eq refl)
    = refl
  unfoldε-functional (fp op x ψ) .(var _ _) (_ , uv-eq refl) (_ , uv-neq ¬refl)
    = ⊥-elim (¬refl refl)
  unfoldε-functional (fp op x ψ) .(var _ _) (_ , uv-neq ¬refl) (_ , uv-eq refl)
    = ⊥-elim (¬refl refl)
  unfoldε-functional (fp op x ψ) (var y y∈Γ) (_ , uv-neq x≢y) (_ , uv-neq x≢y')
    = cong (λ p → _ , uv-neq p) (funext (λ x≡y → ⊥-elim (x≢y x≡y)))
  unfoldε-functional (fp op x ψ) .(μMLη _ _ _) (_ , uη-eq refl) (_ , uη-eq refl)
    = refl
  unfoldε-functional (fp op x ψ) .(μMLη _ _ _) (_ , uη-eq refl) (_ , uη-neq ¬refl W)
    = ⊥-elim (¬refl refl)
  unfoldε-functional (fp op x ψ) .(μMLη _ _ _) (_ , uη-neq ¬refl V) (_ , uη-eq refl)
    = ⊥-elim (¬refl refl)
  unfoldε-functional {Γ} (fp op x ψ) (μMLη op' y ϕ) (_ , uη-neq x≢y V) (_ , uη-neq x≢y' W)
    = cong₂ (λ { (s , gs) eq → μMLη op' y s , uη-neq eq gs }) (unfoldε-functional (fp op x ψ) (subst μMLε (≈L→≡ (insert-comm y x Γ)) ϕ) (_ , V) (_ , W)) (funext (λ x≡y → ⊥-elim (x≢y x≡y)))

-- With all that said, we can throw away the relation and keep the unfolding that we compute:
unfoldε : ∀ {Γ} {ψ' : μMLε []}
        -> (ψ : μFPε ψ') -- the original fixpoint formula that we will substitute for occurrences of z
        -> (ϕ : μMLε (insert (binderOfε ψ) Γ)) -- the formula to traverse. It is a proper subformula of ψ, so must have ψ's binder in scope
        -> {Acc _<ℕ_ (lenε ϕ)}
        -> μMLε Γ
unfoldε ψ ϕ {rs} = proj₁ (unfoldε-computable ψ ϕ {rs})

-- Now saying what it *really* means to unfold a fixpoint formula.
-- This is the one that corresponds to the book definition.
unfoldFpε : {ψ' : μMLε []} -> (ψ : μFPε ψ') -> {Acc _<ℕ_ (lenε ψ')} -> μMLε []
unfoldFpε (fp op x ψ) {acc rs} = unfoldε (fp op x ψ) ψ {rs (lenε ψ) (s≤s ≤-refl)}

--------------------------
-- Defining the Closure --
--------------------------

-- A lemma that probably exists in stdlib (or is a special case of something
-- that does) but was easier to prove than it was to locate.
+lem : ∀ {n n' m m'} -> n ≤ n' -> m ≤ m' -> (n + m) ≤ (n' + m')
+lem z≤n z≤n = z≤n
+lem {zero} {n'} {suc m} {suc m'} z≤n (s≤s y) rewrite +-comm n' (suc m') = s≤s (≤-trans y (m≤m+n m' n'))
+lem {suc n} {suc n'} {zero} {m'} (s≤s x) z≤n rewrite +-comm n 0 = s≤s (≤-trans x (m≤m+n n' m'))
+lem (s≤s x) (s≤s y) = s≤s (+lem x (s≤s y))

-- closureε' : (ψ : μMLε []) -> {Acc _<ℕ_ (lenε ψ)} -> Listμε.SortedList
-- closureε' (μML₀ op) { acc rs }
--   = (μML₀ op) ∷# []
-- closureε' (μML₁ op ψ) { acc rs }
--   = Listμε.insert (μML₁ op ψ)
--                   (closureε' ψ { rs (lenε ψ) (s≤s ≤-refl) })
-- closureε' (μML₂ op ψ ϕ) { acc rs }
--   = Listμε.insert (μML₂ op ψ ϕ)
--                   (closureε' ψ { rs (lenε ψ) (s≤s (m≤m+n (lenε ψ) (lenε ϕ))) } Listμε.∪ closureε' ϕ { rs (lenε ϕ) (s≤s (m≤n+m (lenε ϕ) (lenε ψ))) })
-- closureε' (μMLη op x ψ) { acc rs }
--   =  Listμε.insert (μMLη op x ψ)
--                    (closureε' (unfoldFpε (fp op x ψ) {acc rs}) { rs (lenε (unfoldFpε (fp op x ψ) {acc rs})) (s≤s (lenε-wfη (fp op x ψ) ψ) ) } )
-- closureε' (ε ψ) { acc rs }
--   = []
