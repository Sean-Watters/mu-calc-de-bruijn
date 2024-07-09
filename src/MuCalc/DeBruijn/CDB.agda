module MuCalc.DeBruijn.CDB where

open import MuCalc.DeBruijn.Base using (Op₀; Op₁; Op₂; Opη)
open import Data.Nat
open import Data.Fin as F using (Fin)
open import Data.Bool using (Bool; true; false; T)
open import Data.Unit using (⊤; tt)

data Scope (K : Set) : Set where
  [] : Scope K
  _-,_ : Scope K → K → Scope K
infixl 20 _-,_

length : ∀ {K} → Scope K → ℕ
length [] = zero
length (xs -, x) = suc (length xs)

-- Thinnings!
data _⊑_ {K : Set} : Scope K → Scope K → Set where
  skip : ∀{is j js} → is ⊑ js → is ⊑ (js -, j)
  select : ∀ {i is j js} → is ⊑ js → (is -, i) ⊑ (js -, j)
  zero : [] ⊑ []

data Cover {K : Set} (ov : Bool) : {is js ks : Scope K} → is ⊑ ks → js ⊑ ks → Set where
  done : Cover ov zero zero
  left : ∀ {is js ks} {θ : is ⊑ ks} {ϕ : js ⊑ ks} (x : K) → Cover ov θ ϕ → Cover ov {is -, x} {js} {ks -, x} (select θ) (skip ϕ)
  right : ∀ {is js ks} {θ : is ⊑ ks} {ϕ : js ⊑ ks} (x : K) → Cover ov θ ϕ → Cover ov {is} {js -, x} {ks -, x} (skip θ) (select ϕ)
  both : ∀ {is js ks} {θ : is ⊑ ks} {ϕ : js ⊑ ks} {b : T ov} (x : K) → Cover ov θ ϕ → Cover ov {is -, x} {js -, x} {ks -, x} (select θ) (select ϕ)

-- -- Coverings, specialised to nats.
-- data Cover : (k l m : ℕ) → Set where
--   done   : Cover 0 0 0
--   left   : ∀ {k l m} → Cover k l m → Cover (suc k)      l  (suc m)
--   right  : ∀ {k l m} → Cover k l m → Cover      k  (suc l) (suc m)
--   both   : ∀ {k l m} → Cover k l m → Cover (suc k) (suc l) (suc m)

[*] : Scope ⊤
[*] = [] -, tt

-- we're using nats for our scopes for now, but presented as lists of unit to make it easier to do something fancier later
data μML (At : Set) : (Scope ⊤) → Set where
  var : μML At [*]
  μML₀ : (op : Op₀ At) → μML At []
  μML₁ : ∀ {is} (op : Op₁) → (ϕ : μML At is) → μML At is
  μML₂ : ∀ {is js ks ov} {r : is ⊑ ks} {s : js ⊑ ks} → (op : Op₂) → Cover ov r s → (ϕ : μML At is) → (ψ : μML At js) → μML At ks
  μMLη : ∀ {is} → (op : Opη) → (ϕ : μML At (is -, tt)) → μML At is

{-

-- I think instead, we want a proof x∈is, maybe? uhh, think more later...
sub : ∀ {At : Set} {is js ks}
    → (ϕ : μML At is)
    → (x : ⊤)
    → (ψ : μML At js)
    → {p : is ⊑ ks} {q : js ⊑ ks}
    → Cover true p q -- overlap flag set to true because we want to allow the possibility for some overlap between is and js.
    → μML At ks
sub var x ψ {select p} {skip q} (left .tt C) = {!!}
sub var x ψ {skip p} {select q} (right x₁ C) = {!!}
sub var x ψ {select p} {select q} (both .tt C) = {!!}
sub (μML₁ op ϕ) x ψ p = {!!}
sub (μML₂ op x₁ ϕ ϕ₁) x ψ q = {!!}
sub (μMLη op ϕ) x ψ p = {!!}

-- sub var x ψ = ψ
-- sub (μML₁ op ϕ) x ψ = μML₁ op (sub ϕ x ψ)
-- sub {At} {.suc k} {m} (μML₂ {.suc i} {.j} {.suc k} {ov} op (left {i} {j} {k} {r} {s} C) ϕ ξ) x ψ = μML₂ {{!!}} {{!!}} {{!!}} {{!!}} {{!!}} op {!!} {!sub ϕ x ψ!} ξ
-- sub (μML₂ op (right C) ϕ ξ) x ψ = μML₂ op {!!} ϕ {!!}
-- sub (μML₂ op (both C) ϕ ξ) x ψ = μML₂ op {!!} {!!} {!!}
-- sub (μMLη op ϕ) x ψ = {!!}

-}
