
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

-- guarded by construction formulas; g says whether we're in in the scope of a ■/◆
data Guarded (At : Set) {n : ℕ} (Γ : Vec ℕ n) : Set where
  var : (x : Fin n) → {{NonZero (lookup Γ x)}} → Guarded At Γ
  μML₀ : (op : Op₀ At) → Guarded At Γ
  μML₁ : (op : Op₁) → (ϕ : Guarded At {n} ones) → Guarded At Γ
  μML₂ : (op : Op₂) → (ϕ : Guarded At (inc Γ)) → (ψ : Guarded At (inc Γ)) → Guarded At Γ
  μMLη : (op : Opη) → (ϕ : Guarded At (0 ∷ inc Γ)) → Guarded At Γ

GSentence : Set → Set
GSentence At = Guarded At []
