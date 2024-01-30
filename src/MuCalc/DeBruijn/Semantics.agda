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

open import Function
open import Data.Container.Indexed renaming (⟦_⟧ to ⟦_⟧c ; μ to Mu)
open import Data.Fin hiding (_-_)
open import Data.Vec hiding (filter)
open import Data.Nat
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary

-- *Constructive* semantics using Agda sets.
module AgdaSets
  (S : Set) -- A set of states
  (R : S → S → Set) -- A transition relation on S
  (V : At → S → Set) -- A valuation function for propositions at states
  where

  -- Mu : {A : Set} (F : (A → Set) → (A → Set)) → Set
  -- Mu {A} F = (P : A → Set) → (F  P → P) → P

  -- data Mu {n : ℕ} (ϕ : μML (suc n)) (i : Vec (S → Set) n) (s : S) : Set

  -- data Mu ϕ i s where
  --  inn : ⟦ ϕ ⟧ (Mu ϕ i ∷ i) s → Mu ϕ i s

  ⟦_⟧ : ∀ {n} → μML n → Vec (S → Set) n → S → Set
  ⟦ var x ⟧ i s = lookup i x s
  ⟦ μML₀ ⊤' ⟧ _ _ = ⊤
  ⟦ μML₀ ⊥' ⟧ _ _ = ⊥
  ⟦ μML₀ (at p) ⟧ _ s = V p s
  ⟦ μML₀ (¬at p) ⟧ _ s = ¬ (V p s)
  ⟦ μML₁ □ ϕ ⟧ i s = (y : S) → R s y → ⟦ ϕ ⟧ i y
  ⟦ μML₁ ◆ ϕ ⟧ i s = Σ[ y ∈ S ] (R s y) × ⟦ ϕ ⟧ i y
  ⟦ μML₂ ∧ ϕ ψ ⟧ i s = (⟦ ϕ ⟧ i s) × (⟦ ψ ⟧ i s)
  ⟦ μML₂ ∨ ϕ ψ ⟧ i s = (⟦ ϕ ⟧ i s) ⊎ (⟦ ψ ⟧ i s)
  ⟦_⟧ {n} (μMLη μ ϕ) i s = Mu ({!μML n!} ◃ {!!} / {!!}) s -- Mu ϕ i s --λ (X : S → Set) → ⟦ ϕ ⟧ (X ∷ i)
  ⟦ μMLη ν ϕ ⟧ i s = {!!}

-- Finite semantics with sorted lists
module FreshLists
  {L : Set} {_<L_ : L → L → Set} (L-STO : IsPropStrictTotalOrder _≡_ _<L_) -- a STO of labels
  where

  open import Data.FreshList.InductiveInductive
  open import Free.IdempotentCommutativeMonoid.Base L-STO renaming (_∪_ to _∪'_; _∩_ to _∩'_)
  open import Free.IdempotentCommutativeMonoid.Properties L-STO
  open import Algebra.Structure.OICM

  module _
    (S' : SortedList) -- The state space is a sorted list (ie, finite subset) of labels
    (T : ∀ {x} → x ∈ S' → Σ[ y ∈ SortedList ] y ⊆ S') -- The transition function takes a state in S and returns the set of successor states
    (V : At → Σ[ y ∈ SortedList ] y ⊆ S')
    where

    PS = Σ[ y ∈ SortedList ] y ⊆ S'

    -- The type of transitions in the model S
    _->>_ : L → L → Set
    x ->> y = Σ[ p ∈ (x ∈ S') ] (y ∈ proj₁ (T p))

    -- is there a transition x->>y in the model?
    _->>?_ : Decidable _->>_
    x ->>? y with x ∈? S' -- is x in the model?
    ... | no  x∉S = no λ p → x∉S (proj₁ p)
    ... | yes x∈S with y ∈? (proj₁ (T x∈S)) -- is there a transition from x to y?
    ... | yes y∈Tx = yes (x∈S , y∈Tx)
    ... | no  y∉Tx = no λ p → y∉Tx (subst (y ∈_) (cong (proj₁ ∘ T) (∈-irrelevant (IsPropStrictTotalOrder.≈-prop L-STO) (proj₁ p) x∈S)) (proj₂ p))

    filter-ps : (∀ {x} → x ∈ S' → Bool) → PS → PS
    filter-ps f ([] , X⊆S) = [] , λ ()
    filter-ps f (cons x xs x#xs , X⊆S) with f {x} (X⊆S (here refl))
    ... | true = {!!}
    ... | false = {!!}

    -- The full state space
    S : PS
    S = S' , λ z → z

    -- The empty set
    ø : PS
    ø = [] , λ ()

    -- Set difference
    _-_ : PS → PS → PS
    (X , X⊆S) - (Y , Y⊆S) = X -< Y > , ⊆-trans (-<>-subset X Y) X⊆S

    -- Intersection
    _∩_ : PS → PS → PS
    (X , X⊆S) ∩ (Y , Y⊆S) = (X ∩' Y) , ⊆-trans (∩-lowerboundˡ X Y) X⊆S

    -- Union
    _∪_ : PS → PS → PS
    (X , X⊆S) ∪ (Y , Y⊆S) = (X ∪' Y) , ∪-lub X⊆S Y⊆S

    -- semantics with sorted lists:
    ⟦_⟧ : ∀ {n}
        → μML n -- The formula we are interpreting
        → Vec PS n -- The interpretations of the free variables
        → PS -- The states where the formula is true.
    ⟦ var x ⟧ i = lookup i x
    ⟦ μML₀ ⊤' ⟧ _ = S -- All states
    ⟦ μML₀ ⊥' ⟧ _ = ø -- No states
    ⟦ μML₀ (at p) ⟧ _ = V p -- States given by V
    ⟦ μML₀ (¬at p) ⟧ _ = S - (V p) -- All states except those given by V
    ⟦ μML₁ □ ϕ ⟧ i = filter-ps □ϕ? S where -- All those states s where ϕ holds at every successor state of s
      □ϕ? : {x : L} → x ∈ S' → Bool
      □ϕ? {s} s∈S = does $ all? (_∈? (proj₁ $ ⟦ ϕ ⟧ i)) (proj₁ $ T s∈S)
    ⟦ μML₁ ◆ ϕ ⟧ i = filter-ps ◆ϕ? S where -- All those states s where ϕ holds at at least one successor state of s
      ◆ϕ? : {x : L} → x ∈ S' → Bool
      ◆ϕ? {s} s∈S = does $ any? (_∈? (proj₁ $ ⟦ ϕ ⟧ i)) (proj₁ $ T s∈S)
    ⟦ μML₂ ∧ ϕ ψ ⟧ i = ⟦ ϕ ⟧ i ∩ ⟦ ψ ⟧ i
    ⟦ μML₂ ∨ ϕ ψ ⟧ i = ⟦ ϕ ⟧ i ∪ ⟦ ψ ⟧ i
    ⟦_⟧ {n} (μMLη μ ϕ) i = {!!}
    ⟦ μMLη ν ϕ ⟧ i = {!!}
