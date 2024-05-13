open import Algebra
open import Data.Product
open import Relation.Binary hiding (Irrelevant)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Structures
open import Relation.Binary.Properties.StrictPartialOrder using (>-strictPartialOrder)
open import Relation.Nullary
open import Data.Empty
open import Data.Sum
open import Function

module Algebra.Structures.Propositional where

record IsPropStrictTotalOrder
  { S : Set }
  ( _≈_ : S → S → Set )
  ( _<_ : S → S → Set )
  : Set where
  constructor MkDto
  field
    isSTO : IsStrictTotalOrder _≈_ _<_
    ≈-prop : ∀ {x y} → Irrelevant (x ≈ y)
    <-prop : ∀ {x y} → Irrelevant (x < y)
  open IsStrictTotalOrder isSTO public

  flip-PSTO : IsPropStrictTotalOrder _≈_ (flip _<_)
  IsStrictTotalOrder.isStrictPartialOrder (isSTO flip-PSTO)
    = StrictPartialOrder.isStrictPartialOrder $ >-strictPartialOrder (record
                                                                        { Carrier = S
                                                                        ; _≈_ = _≈_
                                                                        ; _<_ = _<_
                                                                        ; isStrictPartialOrder = isStrictPartialOrder
                                                                        })
  IsStrictTotalOrder.compare (isSTO flip-PSTO) x y with compare x y
  ... | tri< a ¬b ¬c = tri> ¬c ¬b a
  ... | tri≈ ¬a b ¬c = tri≈ ¬c b ¬a
  ... | tri> ¬a ¬b c = tri< c ¬b ¬a
  ≈-prop flip-PSTO = ≈-prop
  <-prop flip-PSTO = <-prop


record IsPropDecTotalOrder
  { S : Set }
  ( _≈_ : S → S → Set )
  ( _≤_ : S → S → Set )
  : Set where
  constructor MkDto
  field
    isDTO : IsDecTotalOrder _≈_ _≤_
    ≤-prop : ∀ {x y} → Irrelevant (x ≤ y)
  open IsDecTotalOrder isDTO public

record IsPropDecTightApartnessRelation
  { S : Set }
  ( _≈_ : S → S → Set )
  (_#_ : S → S → Set )
  : Set where
  field
    isEquivalence : IsEquivalence _≈_
    isAR : IsApartnessRelation _≈_ _#_
    prop : ∀ {x y} → Irrelevant (x # y)
    tight : Tight _≈_ _#_
    dec : Decidable _#_
  open IsApartnessRelation isAR public
  open IsEquivalence isEquivalence renaming (sym to ≈-sym) public

  eqOrApart : (x y : S) → x ≈ y ⊎ x # y
  eqOrApart x y with dec x y
  ... | yes x#y = inj₂ x#y
  ... | no ¬x#y = inj₁ (proj₁ (tight x y) ¬x#y)


module _ {X : Set}{_≈_ : X → X → Set}{_#_ : X → X → Set}
         (isEq : IsEquivalence _≈_)(isAp : IsApartnessRelation _≈_ _#_)
         (isProp : ∀ {x y} → Irrelevant (x # y))
       where

  open IsPropDecTightApartnessRelation

  -- An apartness relation is tight and decidable iff it has the
  -- eqOrApart property. Above we derived it from decidability +
  -- tightness, here we go the other way.
  eqOrApart→DecTight : ((x y : X) → x ≈ y ⊎ x # y) → IsPropDecTightApartnessRelation _≈_ _#_
  isEquivalence (eqOrApart→DecTight p) = isEq
  isAR (eqOrApart→DecTight p) = isAp
  prop (eqOrApart→DecTight p) = isProp
  proj₁ (tight (eqOrApart→DecTight p) x y) ¬x#y with p x y
  ... | inj₁ x=y = x=y
  ... | inj₂ x#y = ⊥-elim (¬x#y x#y)
  proj₂ (tight (eqOrApart→DecTight p) x y) x=y = IsApartnessRelation.irrefl isAp x=y
  dec (eqOrApart→DecTight p) x y with p x y
  ... | inj₁ x=y = no (IsApartnessRelation.irrefl isAp x=y)
  ... | inj₂ x#y = yes x#y

denialApartness : {X : Set} {_≈_ : X → X → Set} → IsEquivalence _≈_ → Decidable _≈_ → IsPropDecTightApartnessRelation {X} _≈_ (λ x y → ¬ x ≈ y)
denialApartness {X} {_≈_} isEq ≡-dec =
  eqOrApart→DecTight isEq apartness (λ p q → refl) eqOrApart
  where
    apartness : IsApartnessRelation _≈_ (λ x y → x ≈ y → ⊥)
    IsApartnessRelation.irrefl apartness x≡y ¬x≡y = ¬x≡y x≡y
    IsApartnessRelation.sym apartness ¬x≡y y≡x = ¬x≡y (IsEquivalence.sym isEq y≡x )
    IsApartnessRelation.cotrans apartness {x} {y} ¬x≡y z with ≡-dec x z | ≡-dec z y
    ... | yes x≡z | yes z≡y = ⊥-elim (¬x≡y (IsEquivalence.trans isEq x≡z z≡y))
    ... | yes x≡z | no ¬z≡y = inj₂ ¬z≡y
    ... | no ¬x≡z | _ = inj₁ ¬x≡z
    eqOrApart : (x y : X) → (x ≈ y) ⊎ (x ≈ y → ⊥)
    eqOrApart x y with ≡-dec x y
    ... | yes x=y = inj₁ x=y
    ... | no ¬x=y = inj₂ ¬x=y

-- NB: **Necessarily** strictly ordered when idempotent, non-strict when not.
record IsOrderedCommutativeMonoid
  { S : Set }
  ( _≈_ : S → S → Set )
  ( _≤_ : S → S → Set )
  ( _∙_ : S → S → S )
  ( ε : S )
  : Set where
  field
    isICM : IsCommutativeMonoid _≈_ _∙_ ε
    isPDTO : IsPropDecTotalOrder _≈_ _≤_
  open IsPropDecTotalOrder isPDTO
  open IsCommutativeMonoid isICM hiding (refl; sym; trans) public

record IsOrderedIdempotentCommutativeMonoid
  { S : Set }
  ( _≈_ : S → S → Set )
  ( _<_ : S → S → Set )
  ( _∙_ : S → S → S )
  ( ε : S )
  : Set where
  field
    isICM : IsIdempotentCommutativeMonoid _≈_ _∙_ ε
    isSTO : IsPropStrictTotalOrder _≈_ _<_

    -- This is a sensible thing to ask, but is not true for sorted lists with lexicographic order.
    -- ∙-preservesˡ-< : ∀ {a b} x → a < b → (x ∙ a) < (x ∙ b)

    -- This is also too strong, but might be an interesting thing to think about.
    -- ε-minimal : ∀ {a} → ε ≢ a → ε < a

  open IsStrictTotalOrder
  open IsIdempotentCommutativeMonoid hiding (refl; sym; trans) public

record IsLeftRegularMonoidWithPropDecApartness
  { S : Set }
  ( _≈_ : S → S → Set )
  ( _#_ : S → S → Set )
  ( _∙_ : S → S → S )
  ( ε : S )
  : Set where
  field
    isICM : IsMonoid _≈_ _∙_ ε
    leftregular : (x y : S) → ((x ∙ y) ∙ x) ≈ (x ∙ y)
    isApartness : IsPropDecTightApartnessRelation _≈_ _#_

  open IsPropDecTightApartnessRelation isApartness public
  open IsMonoid isICM hiding (refl; sym; trans; reflexive; isPartialEquivalence) public
