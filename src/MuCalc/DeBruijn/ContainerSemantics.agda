
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

open import Level
open import Data.Fin hiding (_-_)
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
open import Data.Container.Indexed renaming (⟦_⟧ to `⟦_⟧` ; μ to Mu)
open import Relation.Nullary
open import Relation.Binary

open import MuCalc.DeBruijn.Base <A-STO At-countable renaming (⊤ to ⊤'; ⊥ to ⊥')


{-
  record Container {i} (I : Set i) (c r : Level) :
                   Set (i ⊔ suc c ⊔ suc r) where
    constructor _◃_/_
    field
      Shape  : (i : I) → Set c
      Position : ∀ {i} → Shape i → Set r

  -- The semantics ("extension") of an indexed container.
    `⟦_⟧` : ∀ {i c r ℓ} {I : Set i} → Container I c r →
        Pred I ℓ → Pred I _
  `⟦ C ◃ R ⟧` X o = Σ[ c ∈ C o ] ((r : R c) → X (n c r))

-}

mkUnary : ∀ {n} → Container (S × Fin n) S 0ℓ 0ℓ → Container S S  0ℓ 0ℓ
mkUnary (C ◃ R / n) = C ◃ R / {!!}

interpretVec : ∀ {n} → Vec (S → Set) n → (S × Fin n → Set)
interpretVec xs (s , m) = lookup xs m s

interpretVec' : ∀ {n} → Vec (S → Set) n → (S → Vec Set n)
interpretVec' [] s = []
interpretVec' (x ∷ xs) s = (x s) ∷ (interpretVec' xs s)

mkCont : {n : ℕ} → μML n → Container (S × Fin n) S 0ℓ 0ℓ
mkCont {n} (var x) = (λ s → ⊤) ◃ (λ _ → ⊤) / λ {s} _ _ → s , x
mkCont (μML₀ ⊤') = (λ _ → ⊤) ◃ (λ _ → ⊥) / λ _ ()
mkCont (μML₀ ⊥') = (λ _ → ⊥) ◃ (λ ()) / λ ()
mkCont (μML₀ (at x)) = V x ◃ (λ _ → ⊥) / λ _ ()
mkCont (μML₀ (¬at x)) = (λ s → ¬ (V x s)) ◃ (λ _ → ⊥ ) / λ _ ()
mkCont (μML₁ □ ϕ) = {!!}
mkCont (μML₁ ◆ ϕ) = {!!}
mkCont (μML₂ ∧ ϕ ψ) = {!!}
mkCont (μML₂ ∨ ϕ ψ) = {!!}
mkCont {n} (μMLη μ ϕ) = Mu {!mkCont ϕ!} ◃ {!!} / {!!}
mkCont (μMLη ν ϕ) = {!!}


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
