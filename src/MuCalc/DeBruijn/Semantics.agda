open import Algebra.Structure.OICM
open import Relation.Unary.Countable
open import Relation.Binary.PropositionalEquality

module MuCalc.DeBruijn.Semantics
  {At : Set}
  {_<A_ : At → At → Set}
  (<A-STO : IsPropStrictTotalOrder _≡_ _<A_)
  (At-countable : IsCountable At)
  where

open import MuCalc.DeBruijn.Base <A-STO At-countable renaming (⊤ to ⊤'; ⊥ to ⊥')

open import Data.Fin
open import Data.Vec
open import Data.Nat
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Relation.Nullary

-- *Constructive* semantics using Agda sets.
-- Agda sets do not form a complete lattice; we can
-- only have finitary products and sums. So, we also
-- restrict to only finite state spaces.
module AgdaSets
  (S : Set) -- A set of states
  (R : S → S → Set) -- A transition relation on S
  (V : At → S → Set) -- A valuation function for propositions at states
  where


  data Mu {n : ℕ} (ϕ : μML (suc n)) (i : Fin n → S → Set) (s : S) : Set
  ⟦_⟧ : ∀ {n} → μML n → (Fin n → S → Set) → S → Set
  finCons : {n : ℕ} → (μML (suc n)) → (Fin n → S → Set) → (Fin (suc n) → S → Set)

  finCons ϕ i zero = Mu ϕ i
  finCons ϕ i (suc n) = i n

  data Mu ϕ i s where
   inn : ⟦ ϕ ⟧ (finCons ϕ i) s → Mu ϕ i s

  ⟦ var x ⟧ i s = i x s
  ⟦ μML₀ ⊤' ⟧ _ _ = ⊤
  ⟦ μML₀ ⊥' ⟧ _ _ = ⊥
  ⟦ μML₀ (at p) ⟧ _ s = V p s
  ⟦ μML₀ (¬at p) ⟧ _ s = ¬ (V p s)
  ⟦ μML₁ □ ϕ ⟧ i s = (y : S) → R s y → ⟦ ϕ ⟧ i y
  ⟦ μML₁ ◆ ϕ ⟧ i s = Σ[ y ∈ S ] (R s y) × ⟦ ϕ ⟧ i y
  ⟦ μML₂ ∧ ϕ ψ ⟧ i s = (⟦ ϕ ⟧ i s) × (⟦ ψ ⟧ i s)
  ⟦ μML₂ ∨ ϕ ψ ⟧ i s = (⟦ ϕ ⟧ i s) ⊎ (⟦ ψ ⟧ i s)
  ⟦ μMLη μ ϕ ⟧ i s = Mu ϕ i s --λ (X : S → Set) → ⟦ ϕ ⟧ (X ∷ i)  
  ⟦ μMLη ν ϕ ⟧ i s = {!!}

{-
  data Mu {n : ℕ} (ϕ : μML (suc n)) (i : Vec (S → Set) n) (s : S) : Set
  ⟦_⟧ : ∀ {n} → μML n → Vec (S → Set) n → S → Set

  {-# NO_POSITIVITY_CHECK #-}
  data Mu ϕ i s where
   inn : ⟦ ϕ ⟧ (Mu ϕ i ∷ i) s → Mu ϕ i s



  ⟦ var x ⟧ i s = lookup i x s
  ⟦ μML₀ ⊤' ⟧ _ _ = ⊤
  ⟦ μML₀ ⊥' ⟧ _ _ = ⊥
  ⟦ μML₀ (at p) ⟧ _ s = V p s
  ⟦ μML₀ (¬at p) ⟧ _ s = ¬ (V p s)
  ⟦ μML₁ □ ϕ ⟧ i s = (y : S) → R s y → ⟦ ϕ ⟧ i y
  ⟦ μML₁ ◆ ϕ ⟧ i s = Σ[ y ∈ S ] (R s y) × ⟦ ϕ ⟧ i y
  ⟦ μML₂ ∧ ϕ ψ ⟧ i s = (⟦ ϕ ⟧ i s) × (⟦ ψ ⟧ i s)
  ⟦ μML₂ ∨ ϕ ψ ⟧ i s = (⟦ ϕ ⟧ i s) ⊎ (⟦ ψ ⟧ i s)
  ⟦ μMLη μ ϕ ⟧ i s = Mu ϕ i s --λ (X : S → Set) → ⟦ ϕ ⟧ (X ∷ i)
  ⟦ μMLη ν ϕ ⟧ i s = {!!}
  -}
