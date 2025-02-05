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

open import Function using (_∘_; _$_)

open import MuCalc.Base

-- This file follows PLFA (Wadler, Kokke, and Siek, 2022), except here
-- we tabulate all finite functions.


---------------------------
-- Parallel Substitution --
---------------------------


-- Rescopings are maps of variables, morally speaking.
-- We tabulate the function as a vector to avoid dealing with funext.
Rename : ℕ → ℕ → Set
Rename i j = Vec (Fin j) i

-- A substitution is a map `Fin n → μML At m`, morally speaking.
-- So our substitutions are sequences of formulas, where each formulas position
-- in the sequence tells us which variable it will be substituted at.
Subst : Set → ℕ → ℕ → Set
Subst At i j = Vec (μML At j) i

-- Rescoping extension
ext : ∀ {i j} → Rename i j → Rename (suc i) (suc j)
ext ρ = F.zero ∷ V.map F.suc ρ

-- Executing a renaming
rename : ∀ {At i j} → Rename i j -- if we have an mapping of i vars to j vars...
        → μML At i → μML At j -- then we can map it over an i-term to get a j-term.
rename ρ (var x) = var (V.lookup ρ x)
rename ρ (μML₀ op) = μML₀ op
rename ρ (μML₁ op ϕ) = μML₁ op (rename ρ ϕ)
rename ρ (μML₂ op ϕ ψ) = μML₂ op (rename ρ ϕ) (rename ρ ψ)
rename ρ (μMLη op ϕ) = μMLη op (rename (ext ρ) ϕ)

-- Substitution extension
exts : ∀ {At i j} → Subst At i j → Subst At (suc i) (suc j)
exts σ = (var F.zero) ∷ V.map (rename (V.tabulate F.suc)) σ

-- Executing a parallel substitution
⟪_⟫_ : ∀ {At i j} → Subst At i j → μML At i → μML At j
⟪ σ ⟫ (var x) = V.lookup σ x
⟪ σ ⟫ (μML₀ op) = μML₀ op
⟪ σ ⟫ (μML₁ op ϕ) = μML₁ op (⟪ σ ⟫ ϕ)
⟪ σ ⟫ (μML₂ op ϕ ψ) = μML₂ op (⟪ σ ⟫ ϕ) (⟪ σ ⟫ ψ)
⟪ σ ⟫ (μMLη op ϕ) = μMLη op (⟪ exts σ ⟫ ϕ)

infixr 7 ⟪_⟫_

-----------------------------------
-- The σ-Algebra of Substitution --
-----------------------------------

-- The identity substitution, which substitutes every variable for itself.
ids : ∀ {At i} → Subst At i i
ids = V.tabulate var


-- The "shift" substitution, which shifts every variable up by 1.
-- So 0↦1, 1↦2, etc
↑ : ∀ {At i} → Subst At i (suc i)
↑ = V.tabulate (var ∘ F.suc)

-- Substitution composition; we apply the substitution τ to every element of σ.
_⨟_ : ∀ {At i j k} → Subst At i j → Subst At j k → Subst At i k
σ ⨟ τ = V.map ⟪ τ ⟫_ σ

infixr 6 _⨟_

{-

-- The 4th operation of the algebra is the "cons" substitution, which substitutes the
-- head at zero and the tail elsewhere. Since we're in a tabulated setting, this really
-- is cons for vectors. So rather than introducing a new name, we'll just be using _∷_
_•_ : ∀ {At n m} → μML At m → Subst At n m → Subst At (suc n) m
(ϕ • σ) = ϕ ∷ σ

-}

----------------------------------------
-- Relating Renaming and Substitution --
----------------------------------------

ren : ∀ {At i j} → Rename i j → Subst At i j
ren ρ = V.map (V.lookup ids) ρ

rename-suc : ∀ {At i} (x : Fin i) → var (F.suc x) ≡ rename {At} (V.tabulate F.suc) (V.lookup ids x)
rename-suc x =
  begin
    var (F.suc x)
  ≡⟨ cong var (sym $ lookup∘tabulate F.suc x) ⟩
    rename (V.tabulate F.suc) (var x)
  ≡⟨ cong (rename _) (sym $ lookup∘tabulate var x) ⟩
    rename (V.tabulate F.suc) (V.lookup (V.tabulate var) x)
  ≡⟨⟩
    rename (V.tabulate F.suc) (V.lookup ids x)
  ∎ where open ≡-Reasoning

ren-ext : ∀ {At i j} → (ρ : Rename i j) → ren {At} (ext ρ) ≡ exts (ren ρ)
ren-ext ρ = cong (var F.zero ∷_) $
  begin
    V.map (V.lookup ids) (V.map F.suc ρ)
  ≡⟨ sym (map-∘ (V.lookup ids) F.suc ρ) ⟩
    V.map (V.lookup ids ∘ F.suc) ρ
  ≡⟨ map-cong (λ x → trans (lookup∘tabulate (var ∘ F.suc) x) (rename-suc x)) ρ ⟩
    V.map (rename (V.tabulate F.suc) ∘ V.lookup ids) ρ
  ≡⟨ map-∘ (rename (V.tabulate F.suc)) (V.lookup ids) ρ ⟩
    V.map (rename (V.tabulate F.suc)) (V.map (V.lookup ids) ρ)
  ≡⟨⟩
    V.map (rename (V.tabulate F.suc)) (ren ρ)
  ∎ where open ≡-Reasoning

rename-subst-ren : ∀ {At i j} → (ρ : Rename i j) (ϕ : μML At i)
                 → rename ρ ϕ ≡ ⟪ ren ρ ⟫ ϕ
rename-subst-ren ρ (var x) =
  begin
    rename ρ (var x)
  ≡⟨⟩
    var (V.lookup ρ x)
  ≡⟨ sym $ lookup-map x var ρ ⟩
    V.lookup (V.map var ρ) x
  ≡⟨ sym $ cong (λ z → V.lookup z x) (map-cong (lookup∘tabulate var) ρ) ⟩
    V.lookup (V.map (V.lookup (V.tabulate var)) ρ) x
  ≡⟨⟩
    ⟪ ren ρ ⟫ var x
  ∎ where open ≡-Reasoning
rename-subst-ren ρ (μML₀ op) = refl
rename-subst-ren ρ (μML₁ op ϕ) = cong (μML₁ op) (rename-subst-ren ρ ϕ)
rename-subst-ren ρ (μML₂ op ϕl ϕr) = cong₂ (μML₂ op) (rename-subst-ren ρ ϕl) (rename-subst-ren ρ ϕr)
rename-subst-ren ρ (μMLη op ϕ) = cong (μMLη op) $
  begin
    rename (ext ρ) ϕ
  ≡⟨ rename-subst-ren (ext ρ) ϕ ⟩
    ⟪ ren (ext ρ) ⟫ ϕ
  ≡⟨ cong (⟪_⟫ ϕ) (ren-ext ρ) ⟩
    ⟪ exts (ren ρ) ⟫ ϕ
  ∎ where open ≡-Reasoning

ren-shift : ∀ {At i} → ren {At} {i} {suc i} (V.tabulate F.suc) ≡ ↑
ren-shift {At} {i} = {!!}


----------------
-- Properties --
----------------

-- The easy equations
--------

-- The head of the sequence is substituted at the variable zero.
sub-head : ∀ {At i j} → (σ : Subst At (suc i) j)
         → ⟪ σ ⟫ (var F.zero) ≡ V.head σ
sub-head (ϕ ∷ σ) = refl

-- Precomposing shift returns the tail.
sub-tail : ∀ {At i j} → (σ : Subst At (suc i) j)
         → ↑ ⨟ σ ≡ V.tail σ
sub-tail (ϕ ∷ σ) = trans (sym (tabulate-∘ ⟪ ϕ ∷ σ ⟫_ (var ∘ F.suc))) (tabulate∘lookup σ)

-- Consing together the head and tail gives the original susbtitution.
sub-η : ∀ {At i j} → (σ : Subst At (suc i) j)
      → (⟪ σ ⟫ (var F.zero)) ∷ (↑ ⨟ σ) ≡ σ
sub-η (ϕ ∷ σ) = cong₂ _∷_ (sub-head (ϕ ∷ σ)) (sub-tail (ϕ ∷ σ))

-- Precomposing zero to shift gives the identity substitution.
zero-shift : ∀ {At i} → (var F.zero) ∷ ↑ ≡ ids {At} {suc i}
zero-shift = refl

-- The identity substitution really is the (left) identity of composition.
sub-idL : ∀ {At i j} → (σ : Subst At i j)
        → ids ⨟ σ ≡ σ
sub-idL [] = refl
sub-idL (ϕ ∷ σ) = cong (ϕ ∷_) (sub-tail (ϕ ∷ σ))

-- Post-composition distributes through cons.
sub-dist : ∀ {At i j k} → (σ : Subst At i j) (τ : Subst At j k) (ϕ : μML At j)
         → (ϕ ∷ σ) ⨟ τ ≡ (⟪ τ ⟫ ϕ) ∷ (σ ⨟ τ)
sub-dist σ τ ϕ = refl



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
