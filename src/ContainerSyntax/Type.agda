-- {-# OPTIONS --rewriting #-}
module ContainerSyntax.Type where

open import Level renaming (suc to lsuc)
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.String
open import Data.Product
open import Data.Sum
open import Data.Fin


data Ty (n : ℕ) : Set₁ where
-- Base types ⊥ and ⊤
  `0` `1` : Ty n

-- Binary sum and product
  _`+`_ _`×`_ : Ty n → Ty n → Ty n

-- Indexed sum/dependent pair/sigma types
-- Boo, this bumps up the size :( not a problem, just annoying
  `Σ` : (X : Set) → (X → Ty n) → Ty n

-- LFP and GFP
  `μ`_ : Ty (suc n) → Ty n
  `ν`_ : Ty (suc n) → Ty n

-- Fixpoint variables
  `var` : Fin n → Ty n

infixl 20 _`+`_
infixl 20 _`×`_
infix 0 `μ`_
-- infix 0 `ν`_

---------------------------------------------

-- Views --

data Product : {n : ℕ} → Ty n → Set₁ where
  _`×`_ : ∀ {n} → (l r : Ty n) → Product (l `×` r)

ProdL : ∀ {n} {ty : Ty n} → Product ty → Ty n
ProdL (l `×` r) = l

ProdR : ∀ {n} {ty : Ty n} → Product ty → Ty n
ProdR (l `×` r) = r

data Sum : {n : ℕ} → Ty n → Set₁ where
  _`+`_ : ∀ {n} → (l r : Ty n) → Sum (l `+` r)

SumL : ∀ {n} {ty : Ty n} → Sum ty → Ty n
SumL (l `+` r) = l

SumR : ∀ {n} {ty : Ty n} → Sum ty → Ty n
SumR (l `+` r) = r

data Sigma : {n : ℕ} → Ty n → Set₁ where
  `Σ` : ∀ {n} (X : Set) → (f : X → Ty n) → Sigma (`Σ` X f)

SigmaL : ∀ {n} {ty : Ty n} → Sigma ty → Set
SigmaL (`Σ` l r) = l

SigmaR : ∀ {n} {ty : Ty n} → (p : Sigma ty) → (SigmaL p → Ty n)
SigmaR (`Σ` l r) = r

data Mu : {n : ℕ} → Ty n → Set₁ where
  `μ`_ : ∀ {n} → (t : Ty (suc n)) → Mu (`μ` t)

MuSup : ∀ {n} {ty : Ty n} → Mu ty → Ty (suc n)
MuSup (`μ` ty) = ty

-- data Nu : {n : ℕ} → Ty n → Set₁ where
--   `ν`_ : ∀ {n} → (t : Ty (suc n)) → Nu (`ν` t)



data Inductive : {n : ℕ} → Ty n → Set₁ where
  `0` : ∀ {n} → Inductive {n} `0`
  `1` : ∀ {n} → Inductive {n} `1`
  _`+`_ : ∀ {n} → {l r : Ty n} → Inductive l → Inductive r → Inductive (l `+` r)
  _`×`_ : ∀ {n} → {l r : Ty n} → Inductive l → Inductive r → Inductive (l `×` r)
  `Σ` : ∀ {n} (X : Set) → {f : X → Ty n} → (∀ x → Inductive (f x)) → Inductive (`Σ` X f)
  `μ`_ : ∀ {n} → {t : Ty (suc n)} → Inductive t → Inductive (`μ` t)
  `var` : ∀ {n} → (x : Fin n) → Inductive (`var` x)

data Fixpointless : {n : ℕ} → Ty n → Set₁ where
  `0` : ∀ {n} → Fixpointless {n} `0`
  `1` : ∀ {n} → Fixpointless {n} `1`
  _`+`_ : ∀ {n} → {l r : Ty n} → Fixpointless l → Fixpointless r → Fixpointless (l `+` r)
  _`×`_ : ∀ {n} → {l r : Ty n} → Fixpointless l → Fixpointless r → Fixpointless (l `×` r)
  `Σ` : ∀ {n} (X : Set) → {f : X → Ty n} → (∀ x → Fixpointless (f x)) → Fixpointless (`Σ` X f)
  `var` : ∀ {n} → (x : Fin n) → Fixpointless (`var` x)


data SimpleInductive : {n : ℕ} → Ty n → Set₁ where
  `μ`_ : ∀ {n} {t : Ty (suc n)} → Fixpointless t → SimpleInductive (`μ` t)



---------------------------------------------

-- Telescopes are vectors of elements of a ℕ-indexed family F, where the index of the elements stored
-- in the vector increse telescopically. You could generalise this to more interesting scopes than ℕ,
-- of course.
data Context : ℕ → Set₁ where
  [] : Context 0
  _-,_ : ∀ {n} → Context n → Ty n → Context (suc n)

data All {ℓ : Level} (P : {n : ℕ} → Ty n → Set ℓ) : ∀ {n} → Context n → Set (lsuc ℓ) where
  [] : All P []
  _-,_ : ∀ {n} {ty : Ty n} {tys : Context n} → All P tys → P ty → All P (tys -, ty)


lookup : ∀ {n} → Context n → (x : Fin n) → Ty (n ℕ-ℕ (suc x))
lookup (Γ -, ty) Fin.zero = ty
lookup (Γ -, ty) (suc x) = lookup Γ x

unwind : ∀ {n} → Context n → (x : Fin n) → Context (n ℕ-ℕ (suc x))
unwind (Γ -, ty) Fin.zero = Γ
unwind (Γ -, ty) (suc x) = unwind Γ x

-- -- For some reason you can only overload names if theyre both constructors or both pattern synonyms, so
-- -- we have to do it this way in order to also have this as a pattern synonym for lists
-- pattern _-,_ sx x = tcons x sx
-- infixl 20 _-,_

---------------------------------------------

`Set` : Set₁
`Set` = Ty 0
