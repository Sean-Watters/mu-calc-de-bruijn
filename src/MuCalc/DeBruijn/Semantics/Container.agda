{-# OPTIONS --sized-types #-}

open import Algebra.Structures.Propositional
open import Relation.Binary.PropositionalEquality
open import Data.Kripke

-- The type-theoretic semantics of the modal mu calculus, realised by containers.
-- We chose Sized Types as the foundation for coinduction.
module MuCalc.DeBruijn.Semantics.Container
  {At : Set}
  {_<A_ : At → At → Set}
  (<A-STO : IsPropStrictTotalOrder _≡_ _<A_)
  (Mo : Kripke At)
  where

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional using (Extensionality) renaming (implicit-extensionality to exti)
open import Data.Fin using (Fin; _≟_) renaming (zero to fzero; suc to fsuc)
open import Data.Vec using (Vec; lookup)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Container.Indexed.Fam renaming (⟦_⟧ to ⟨⟦_⟧⟩)
open import Data.Container.Indexed.Fam.SizedTypes
open import Data.Container.Indexed.Fam.Correctness

open import Function
open import Relation.Nullary
open import Relation.Binary.Isomorphism
open import MuCalc.DeBruijn.Base renaming (⊤ to ⊤'; ⊥ to ⊥') hiding (¬)

private
  open Kripke renaming (S to S'; _~>_ to R; V to V')
  S = S' Mo
  _~>_ = R Mo
  V = V' Mo
  open Container
------------------------------------------------------------------------------

-- We want to assign meaning to formulas in our Kripke model. For some closed sentence
-- ϕ, ⟦ϕ⟧ is a predicate on the states of the model which identifies the states where ϕ
-- holds.

-- Formulas can contain bound variables, so we must also have a way to compute and retain
-- their meanings along the way. ie, for every bound variable, we assign a predicate on S.
-- Since our formulas use de Bruijn indices, the sensible approach is to use length-indexed
-- vectors to relate variables to their interpretations. Whenever we go under a binder, we
-- append the interpretation of the new variable to the head of the vector, preserving the 1:1
-- mapping between variable names and the index of the corresponding interpretation.

-- Because we are working with indexed containers, we need a way to view our vectors
-- of intepretations of bound variables as a single indexed family of sets. `lookup` gives
-- us exactly this --- by indexing by a pair of a state and a variable name, looking these
-- up in our vector gives us the family we need.
interpret-vec : ∀ {n} → Vec (S → Set) n → (S × Fin n → Set)
interpret-vec xs (s , m) = lookup xs m s

-- When we come to define ⟦μϕ⟧, we need to eventually produce a container indexed by
-- `S × Fin n`. The one given by the recursive call ⟦ϕ⟧ has index `(S × Fin (suc n))`.
-- The maximum amount of generality allowed by the fixpoint combinators of containers #
-- is as follows:
-- The {least/greatest} fixpoint of a container indexed by `I ⊎ J` is indexed by `I`.
-- So if we can write `S × Fin (suc n)` in the form `(S × Fin n) ⊎ S`, then we're happy.
-- And we can, so we are:
-- This boils down to the fact that `S×(n+1) = (S×n)+S`. In particular, we
-- think of the left (S×n) as the intepretation of the variables we already had,
-- and the right (+S) as the interpration of the new variable bound by the μ/ν that
-- we just went under.
--
-- The final detail is that for indexed containers, functoriality in the left index
-- is contravariant. So the direction we actually need is:
dist-fin : ∀ {n} → S × Fin n ⊎ S → S × Fin (suc n)
dist-fin {n} (inj₁ (s , m)) = s , fsuc m
dist-fin {n} (inj₂ s) = s , fzero


-- Now to draw the rest of the owl!
MkCont : {n : ℕ} → μML At n → Container (S × Fin n) S
MkCont {n} (var x) = (const ⊤) ◃ λ { {t} _ (s , y) → x ≡ y × s ≡ t}
MkCont ⊤' = ⟨const⟩ (const ⊤)
MkCont ⊥' = ⟨const⟩ (const ⊥)
MkCont (μML₀ (at x)) = ⟨const⟩ (V x)
MkCont (μML₀ (¬at x)) = ⟨const⟩ (λ s → ¬ (V x s))
MkCont {n} (■ ϕ) = (λ s → (x : Σ[ t ∈ S ] (s ~> t)) → Shape (MkCont ϕ) (proj₁ x))
               ◃ λ { {s} σ x → Σ[ t ∈ S ] Σ[ sRt ∈ (s ~> t) ] Position (MkCont ϕ) (σ (t , sRt)) x }
MkCont (◆ ϕ) = ⟨Σ⟩ {X = λ x → Σ[ y ∈ S ] (x ~> y)} (λ _ → MkCont ϕ)
MkCont (ϕ ∧ ψ) = MkCont ϕ ⟨×⟩ MkCont ψ
MkCont (ϕ ∨ ψ) = MkCont ϕ ⟨+⟩ MkCont ψ
MkCont (μ ϕ) = ⟨μ⟩ (⟨map⟩ dist-fin (MkCont ϕ))
MkCont (ν ϕ) = ⟨ν⟩ (⟨map⟩ dist-fin (MkCont ϕ))

-- And finally, we can give the semantics of formulas with the type we wanted via
-- the extension of the above container.
⟦_⟧ : ∀ {n} → μML At n → Vec (S → Set) n → S → Set
⟦_⟧ {n} ϕ i = ⟨⟦ MkCont ϕ ⟧⟩ (interpret-vec i)

module VarCorrect (ext : Extensionality 0ℓ 0ℓ) where
  var-correct : ∀ {n} (x : Fin n) (i : Vec (S → Set) n) → ⟦ var x ⟧ i ≃ᵢ lookup i x
  to (var-correct x i {s}) (_ , P) = P (refl , refl)
  from (var-correct x i {s}) X = _ , λ { {t , .x} (refl , refl) → X}
  from-to (var-correct x i {s}) (tt , P) = cong (tt ,_) (exti ext (λ { {t , y} → ext (λ { (refl , refl) → refl }) }))
  to-from (var-correct x i {s}) b = refl

module BoxCorrect (ext : Extensionality 0ℓ 0ℓ) where
  correct : ∀ {n} (s : S) (i : Vec (S → Set) n) (ϕ : μML At n)
          → ⟦ ■ ϕ ⟧ i s ≃ ((t : S) → s ~> t → ⟦ ϕ ⟧ i t )
  to (correct s i ϕ) (σ , Q) t sRt = σ (t , sRt) , λ x → Q (t , sRt , x)
  from (correct s i ϕ) σ = (λ { (t , sRt) → proj₁ (σ t sRt)}) , λ { (t , sRt , P) → proj₂ (σ t sRt) P}
  from-to (correct s i ϕ) (σ , Q) = refl
  to-from (correct s i ϕ) b = refl
