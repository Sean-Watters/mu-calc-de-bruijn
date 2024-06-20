
module MuCalc.DeBruijn.Guarded where

open import Data.Nat hiding (_≟_)
open import Data.Fin using (Fin; zero; suc; _≟_) renaming (inject₁ to fin-inject₁)
open import Data.Bool using (Bool; true; false; T)
open import Data.Unit using (tt)
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

open import MuCalc.DeBruijn.Base

ones : ∀ {n} → Vec ℕ n
ones {zero} = []
ones {suc n} = 1 ∷ ones

-- special increment which only affects non-zero entries
inc : ∀ {n} → Vec ℕ n → Vec ℕ n
inc [] = []
inc (zero ∷ xs) = zero ∷ inc xs
inc (suc x ∷ xs) = suc (suc x) ∷ inc xs

-- guarded by construction formulas. Contexts are lists rather than mere nats.
-- The length of the context tells us how many variables we have in scope, a la
-- de Bruijn, meanwhile the values living at each position tell us the distance to the
-- most recent modal operator that guards that variable. We treat a value of 0 as meaning
-- that variable has not been guarded yet, so when we go deeper into the formula tree, only
-- the non-zero values are incremented.
data Guarded (At : Set) {n : ℕ} (Γ : Vec ℕ n) : Set where
  var : (x : Fin n) → {{NonZero (lookup Γ x)}} → Guarded At Γ -- instance resolution solves the guardedness proofs for us
  μML₀ : (op : Op₀ At) → Guarded At Γ
  μML₁ : (op : Op₁) → (ϕ : Guarded At {n} ones) → Guarded At Γ
  μML₂ : (op : Op₂) → (ϕ : Guarded At (inc Γ)) → (ψ : Guarded At (inc Γ)) → Guarded At Γ
  μMLη : (op : Opη) → (ϕ : Guarded At (0 ∷ inc Γ)) → Guarded At Γ

GSentence : Set → Set
GSentence At = Guarded At []


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


-- todo:
-- * DNF is much easier with guardedness
-- * Q: Is guarded actually equivalent to non-guarded with constructive/container semantics?
-- * Q: Does this make computing the closure and proving correctness easier?!
