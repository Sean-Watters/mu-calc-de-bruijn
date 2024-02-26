
open import Algebra.Structures.Propositional
open import Relation.Unary.Countable
open import Relation.Binary.PropositionalEquality

module MuCalc.DeBruijn.ContainerSemantics
  {At : Set}
  {_<A_ : At → At → Set}
  (<A-STO : IsPropStrictTotalOrder _≡_ _<A_)
  (At-countable : IsCountable At)
  -- The model
  (S : Set) -- A set of states
  (R : S → S → Set) -- A transition relation on S
  (V : At → S → Set) -- A valuation function for propositions at states
  where

open import Level renaming (zero to fzero; suc to fsuc)
open import Data.Fin hiding (_-_) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using ()
open import Data.Fin.MoreProps renaming (<-isPropStrictTotalOrder to Fin-STO)
open import Data.Vec hiding (toList; filter; insert)
open import Data.Nat
open import Data.Nat.Properties using ()
open import Data.Nat.MoreProps renaming (<-isPropStrictTotalOrder to ℕ-STO)
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Container.Indexed renaming (Container to Container'; ⟦_⟧ to `⟦_⟧`)
open import Data.Container.Indexed.Combinator using (const) renaming (_×_ to _`×`_; _⊎_ to _`+`_; Π to All; Σ to Any)
open import Relation.Nullary
open import Relation.Binary

open import MuCalc.DeBruijn.Base <A-STO At-countable renaming (⊤ to ⊤'; ⊥ to ⊥')

private
  -- we always want small things, so define an alias where the levels are
  -- fixed at 0
  Container : Set → Set → Set₁
  Container I O = Container' I O 0ℓ 0ℓ

-- mkUnary : ∀ {n} → Container (S × Fin n) S 0ℓ 0ℓ → Container S S  0ℓ 0ℓ
-- mkUnary {m} (C ◃ R / n) = C ◃ (λ c → R c × Fin m) / {!!}

interpretVec : ∀ {n} → Vec (S → Set) n → (S × Fin n → Set)
interpretVec xs (s , m) = lookup xs m s

-- interpretVec' : ∀ {n} → Vec (S → Set) n → (S → Vec Set n)
-- interpretVec' [] s = []
-- interpretVec' (x ∷ xs) s = (x s) ∷ (interpretVec' xs s)

-- might hope these types could be generalised?
Mu : ∀ {n} → Container (S × Fin (suc n)) S → Container (S × Fin n) S
Mu = {!!}

Nu : ∀ {n} → Container (S × Fin (suc n)) S → Container (S × Fin n) S
Nu = {!!}

mkCont : {n : ℕ} → μML n → Container (S × Fin n) S
mkCont {n} (var x) = (λ s → ⊤) ◃ (λ _ → ⊤) / λ {s} _ _ → s , x
mkCont (μML₀ ⊤') = const (λ _ → ⊤)
mkCont (μML₀ ⊥') = const(λ _ → ⊥)
mkCont (μML₀ (at x)) = const (V x)
mkCont (μML₀ (¬at x)) = const (λ s → ¬ (V x s))
-- think the command is correct so far but needs to incorporate a recursive call in
-- the hole. Π's implementation will probably tell us a lot about how it should look
mkCont (μML₁ □ ϕ) = (λ s → ((x : S) → R s x → {!!})) ◃ {!!} / {!!}
mkCont (μML₁ ◆ ϕ) = {!(mkCont ϕ)!}
mkCont (μML₂ ∧ ϕ ψ) = mkCont ϕ `×` mkCont ψ
mkCont (μML₂ ∨ ϕ ψ) = mkCont ϕ `+` mkCont ψ
mkCont (μMLη μ ϕ) = Mu (mkCont ϕ)
mkCont (μMLη ν ϕ) = Nu (mkCont ϕ)

⟦_⟧ : ∀ {n} → μML n → Vec (S → Set) n → S → Set
⟦_⟧ {n} ϕ i = `⟦_⟧` (mkCont ϕ) (interpretVec i)

{-

⟦ var x ⟧ i s = lookup i x s
⟦ μML₀ ⊤' ⟧ _ _ = ⊤
⟦ μML₀ ⊥' ⟧ _ _ = ⊥
⟦ μML₀ (at p) ⟧ _ s = V p s
⟦ μML₀ (¬at p) ⟧ _ s = ¬ (V p s)
⟦ μML₁ □ ϕ ⟧ i s = (y : S) → R s y → ⟦ ϕ ⟧ i y
⟦ μML₁ ◆ ϕ ⟧ i s = Σ[ y ∈ S ] (R s y) × ⟦ ϕ ⟧ i y
⟦ μML₂ ∧ ϕ ψ ⟧ i s = (⟦ ϕ ⟧ i s) × (⟦ ψ ⟧ i s)
⟦ μML₂ ∨ ϕ ψ ⟧ i s = (⟦ ϕ ⟧ i s) ⊎ (⟦ ψ ⟧ i s)
⟦_⟧ {n} (μMLη μ ϕ) i s = Mu ({!μML n!} ◃ {!!} / {!!}) s -- Mu ϕ i s
  -- --λ (X : S → Set) → ⟦ ϕ ⟧ (X ∷ i)
⟦ μMLη ν ϕ ⟧ i s = {!!}

-}
