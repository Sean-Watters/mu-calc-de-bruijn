module Free.IdempotentCommutativeMonoid.Adjunction where

open import Algebra hiding (IdempotentCommutativeMonoid)
open import Function

open import Data.Product hiding (map)
open import Data.Sum
open import Data.Empty
open import Data.Nat renaming (_<_ to _<N_)
open import Data.Nat.Induction
open import Induction.WellFounded

open import Relation.Binary hiding (NonEmpty; StrictTotalOrder)
open import Relation.Binary.PropositionalEquality renaming (isEquivalence to ≡-isEquivalence)
open import Relation.Nullary hiding (Irrelevant)
open import Relation.Nullary.Decidable hiding (map)

open import Data.FreshList.InductiveInductive
open import Free.IdempotentCommutativeMonoid.Base
import Free.IdempotentCommutativeMonoid.Properties as FICM
open import Category.Base
open import Algebra.Structure.OICM

open import Axiom.UniquenessOfIdentityProofs
open import Axiom.Extensionality.Propositional

--------------------------------------------------
-- Algebraic Structure on Sorted Lists
--------------------------------------------------

-- We now instantiate ≈ to be real equality ≡. First we need to do a
-- little plumbing to show that the pointwise lifting ≈L of equality
-- is equality.

module _ {X : Set} {_<_ : X → X → Set} (<-STO : IsPropStrictTotalOrder _≡_ _<_)  where

  open FICM <-STO

  ≈L→≡ : ∀ {xs ys} → _≈L_ xs ys → xs ≡ ys
  ≈L→≡ [] = refl
  ≈L→≡ (cons x=x' xs=xs') = WithIrr.cons-cong _<_ (IsPropStrictTotalOrder.<-prop <-STO) x=x' (≈L→≡ xs=xs')

  Tri≈L→Tri≡ : ∀ {a c lt gt} x y → Tri {a} {c = c} lt (_≈L_  x y) gt -> Tri lt (x ≡ y) gt
  Tri≈L→Tri≡ x y (tri< a ¬b ¬c) = tri< a (λ { refl → ¬b ≈L-refl}) ¬c
  Tri≈L→Tri≡ x y (tri≈ ¬a b ¬c) = tri≈ ¬a (≈L→≡ b) ¬c
  Tri≈L→Tri≡ x y (tri> ¬a ¬b c) = tri> ¬a (λ { refl → ¬b ≈L-refl}) c

  open IsOrderedIdempotentCommutativeMonoid hiding (isICM; isSTO)
  open IsIdempotentCommutativeMonoid
  open IsCommutativeMonoid
  open IsMonoid
  open IsSemigroup
  open IsMagma

  -- we repackage all the structures using the above
  opaque
    unfolding union

    SL-isM : IsMonoid _≡_ (_∪_ <-STO) []
    IsMagma.isEquivalence (IsSemigroup.isMagma (IsMonoid.isSemigroup SL-isM)) = ≡-isEquivalence
    ∙-cong (IsSemigroup.isMagma (IsMonoid.isSemigroup SL-isM)) _≡_.refl _≡_.refl = _≡_.refl
    assoc (IsMonoid.isSemigroup SL-isM) x y z = ≈L→≡ (∪-assoc x y z)
    identity SL-isM = (λ x → _≡_.refl) , ∪-idʳ

    SL-isCM : IsCommutativeMonoid _≡_ (_∪_ <-STO) []
    IsCommutativeMonoid.isMonoid SL-isCM = SL-isM
    comm SL-isCM x y = ≈L→≡ (∪-comm x y)

    SL-isICM : IsIdempotentCommutativeMonoid _≡_ (_∪_ <-STO) []
    isCommutativeMonoid SL-isICM = SL-isCM
    idem SL-isICM x = ≈L→≡ (∪-idempotent x)

    SL-isSTO : IsPropStrictTotalOrder _≡_ _<L_
    IsStrictTotalOrder.isEquivalence (IsPropStrictTotalOrder.isSTO SL-isSTO) = ≡-isEquivalence
    IsStrictTotalOrder.trans (IsPropStrictTotalOrder.isSTO SL-isSTO) = <L-trans
    IsStrictTotalOrder.compare (IsPropStrictTotalOrder.isSTO SL-isSTO) x y = Tri≈L→Tri≡ x y (compareL x y)
    IsPropStrictTotalOrder.≈-prop SL-isSTO
      = Axiom.UniquenessOfIdentityProofs.Decidable⇒UIP.≡-irrelevant
          (WithIrr.lift-decEq _<_ (IsPropStrictTotalOrder.<-prop <-STO) (IsPropStrictTotalOrder._≟_ <-STO))
    IsPropStrictTotalOrder.<-prop SL-isSTO = <L-prop

    SL-isOICM : IsOrderedIdempotentCommutativeMonoid _≡_ _<L_ (_∪_ <-STO) []
    IsOrderedIdempotentCommutativeMonoid.isICM SL-isOICM = SL-isICM
    IsOrderedIdempotentCommutativeMonoid.isSTO SL-isOICM = SL-isSTO


------------------------------------------------------------
-- The Category of Ordered Idempotent Commutative Monoids --
------------------------------------------------------------

record OrderedIdempotentCommutativeMonoid : Set₁ where
  constructor MkOicm
  field
    Carrier : Set
    _<_ : Carrier → Carrier → Set
    _∙_ : Carrier → Carrier → Carrier
    ε : Carrier
    proof : IsOrderedIdempotentCommutativeMonoid _≡_ _<_ _∙_ ε
open OrderedIdempotentCommutativeMonoid

record OicmMorphism (A B : OrderedIdempotentCommutativeMonoid) : Set where
  constructor MkOicmMorphism
  private
    module A = OrderedIdempotentCommutativeMonoid A
    module B = OrderedIdempotentCommutativeMonoid B

  field
    fun : Carrier A → Carrier B
    preserves-ε : fun (A.ε) ≡ B.ε
    preserves-∙ : ∀ x y → fun (x A.∙ y) ≡ (fun x) B.∙ (fun y)
open OicmMorphism

oicm-id : ∀ {A} → OicmMorphism A A
fun oicm-id = Function.id
preserves-ε oicm-id = refl
preserves-∙ oicm-id _ _ = refl

oicm-comp : ∀ {A B C} → OicmMorphism A B → OicmMorphism B C → OicmMorphism A C
fun (oicm-comp f g) = (fun g) ∘ (fun f)
preserves-ε (oicm-comp f g) = trans (cong (fun g) (preserves-ε f)) (preserves-ε g)
preserves-∙ (oicm-comp f g) _ _ = trans (cong (fun g) (preserves-∙ f _ _)) (preserves-∙ g _ _)

eqOicmMorphism : Extensionality _ _ →
                 ∀ {A B} → {f g : OicmMorphism A B} → fun f ≡ fun g → f ≡ g
eqOicmMorphism ext {A} {B} {MkOicmMorphism .f refl p∙} {MkOicmMorphism f q q∙} refl
  = cong₂ (MkOicmMorphism f) (uipB refl q) (ext λ x → ext λ y → uipB (p∙ x y) (q∙ x y))
  where
    uipB = IsPropStrictTotalOrder.≈-prop (IsOrderedIdempotentCommutativeMonoid.isSTO (proof B))

OICM : Extensionality _ _ → Category
Category.Obj (OICM ext) = OrderedIdempotentCommutativeMonoid
Category.Hom (OICM ext) = OicmMorphism
Category.id (OICM ext) = oicm-id
Category.comp (OICM ext) = oicm-comp
Category.assoc (OICM ext) {A} {B} {C} {D} {f} {g} {h} = eqOicmMorphism ext refl
Category.identityˡ (OICM ext) {A} {B} {f} = eqOicmMorphism ext refl
Category.identityʳ (OICM ext) {A} {B} {f} = eqOicmMorphism ext refl

------------------------------------------------------------
-- The Category of Idempotent Commutative Monoids --
------------------------------------------------------------

record IdempotentCommutativeMonoid : Set₁ where
  constructor MkIcm
  field
    Carrier : Set
    _∙_ : Carrier → Carrier → Carrier
    ε : Carrier
    proof : IsIdempotentCommutativeMonoid _≡_ _∙_ ε
    ≡-prop : Irrelevant (_≡_ {A = Carrier})
open IdempotentCommutativeMonoid


record IcmMorphism (A B : IdempotentCommutativeMonoid) : Set where
  constructor MkIcmMorphism
  private
    module A = IdempotentCommutativeMonoid A
    module B = IdempotentCommutativeMonoid B

  field
    fun : A.Carrier → B.Carrier
    preserves-ε : fun (A.ε) ≡ B.ε
    preserves-∙ : ∀ x y → fun (x A.∙ y) ≡ (fun x) B.∙ (fun y)
open IcmMorphism

icm-id : ∀ {A} → IcmMorphism A A
fun icm-id = Function.id
preserves-ε icm-id = refl
preserves-∙ icm-id _ _ = refl

icm-comp : ∀ {A B C} → IcmMorphism A B → IcmMorphism B C → IcmMorphism A C
fun (icm-comp f g) = (fun g) ∘ (fun f)
preserves-ε (icm-comp f g) = trans (cong (fun g) (preserves-ε f)) (preserves-ε g)
preserves-∙ (icm-comp f g) _ _ = trans (cong (fun g) (preserves-∙ f _ _)) (preserves-∙ g _ _)

eqIcmMorphism : Extensionality _ _ →
                 ∀ {A B} → {f g : IcmMorphism A B} → fun f ≡ fun g → f ≡ g
eqIcmMorphism ext {A} {B} {MkIcmMorphism .f refl p∙} {MkIcmMorphism f q q∙} refl
  = cong₂ (MkIcmMorphism f) (uipB refl q) (ext λ x → ext λ y → uipB (p∙ x y) (q∙ x y))
  where
    uipB : Irrelevant (_≡_ {A = Carrier B})
    uipB = ≡-prop  B

ICM : Extensionality _ _ → Category
Category.Obj (ICM ext) = IdempotentCommutativeMonoid
Category.Hom (ICM ext) = IcmMorphism
Category.id (ICM ext) = icm-id
Category.comp (ICM ext) = icm-comp
Category.assoc (ICM ext) {A} {B} {C} {D} {f} {g} {h} = eqIcmMorphism ext refl
Category.identityˡ (ICM ext) {A} {B} {f} = eqIcmMorphism ext refl
Category.identityʳ (ICM ext) {A} {B} {f} = eqIcmMorphism ext refl


-----------------------------------------
-- The Category of Strict Total Orders --
-----------------------------------------

record PropStrictTotalOrder : Set₁ where
  constructor MkSto
  field
    Carrier : Set
    _<_ : Carrier → Carrier → Set
    proof : IsPropStrictTotalOrder _≡_ _<_
open PropStrictTotalOrder

STO : Category
Category.Obj STO = PropStrictTotalOrder
Category.Hom STO X Y = Carrier X → Carrier Y
Category.id STO = id
Category.comp STO f g = g ∘ f
Category.assoc STO = refl
Category.identityˡ STO = refl
Category.identityʳ STO = refl

---------------------------
-- The Forgetful Functor --
---------------------------

open Functor

open IsOrderedIdempotentCommutativeMonoid

FORGET : (ext : Extensionality _ _) → Functor (OICM ext) STO
act (FORGET _) (MkOicm S _<_ _∙_ ε oicm) = MkSto S _<_ (isSTO oicm)
fmap (FORGET _) f = fun f
identity (FORGET _) = refl
homomorphism (FORGET _) = refl

----------------------
-- The Free Functor --
----------------------

SL-map : {X Y : PropStrictTotalOrder} → (Carrier X → Carrier Y) → SortedList (proof X) → SortedList (proof Y)
SL-map f [] = []
SL-map {X} {Y} f (cons x xs fx) = insert (proof Y) (f x) (SL-map {X} {Y} f xs)

SL-map-preserves-∈ : ∀ {X Y : PropStrictTotalOrder} →
                     let _∈X_ = FICM._∈_ (proof X)
                         _∈Y_ = FICM._∈_ (proof Y) in
                     (f : Carrier X → Carrier Y) →
                     (a : Carrier X) (xs : SortedList (proof X)) →
                     a ∈X xs → (f a) ∈Y (SL-map {X} {Y} f xs)
SL-map-preserves-∈ {X} {Y} f a (cons .a xs x#xs) (here refl)
  = FICM.∈∪-introˡ (proof Y) (here refl) (SL-map {X} {Y} f xs)
SL-map-preserves-∈ {X} {Y} f a (cons x xs x#xs) (there p)
  = FICM.∈∪-introʳ (proof Y) (cons (f x) [] []) (SL-map-preserves-∈ {X} {Y} f a xs p)

SL-map-preserves-⊆ : ∀ {X Y : PropStrictTotalOrder} →
           let _⊆X_ = FICM._⊆_ (proof X)
               _⊆Y_ = FICM._⊆_ (proof Y) in
           (f : Carrier X → Carrier Y)
           → (xs ys : SortedList (proof X))
           → xs ⊆X ys
           → (SL-map {X} {Y} f xs) ⊆Y (SL-map {X} {Y} f ys)
SL-map-preserves-⊆ {X} {Y} f (cons x xs x#xs) ys xs⊆ys {a} a∈mapfxxs
  with FICM.∈∪-elim (proof Y) {xs = cons (f x) [] []} {SL-map {X} {Y} f xs} a∈mapfxxs
... | inj₁ (here refl) = SL-map-preserves-∈ f x ys (xs⊆ys {x} (here refl))
... | inj₂ a∈mapfxs = SL-map-preserves-⊆ f xs ys (λ b∈xs → xs⊆ys (there b∈xs)) a∈mapfxs


opaque
  unfolding union

  SL-map-preserves-∪ : {X Y : PropStrictTotalOrder} →
                       let _∪X_ = _∪_ (proof X)
                           _∪Y_ = _∪_ (proof Y) in
                       {f : Carrier X → Carrier Y} →
                       (xs ys : SortedList (proof X)) →
                       SL-map {X} {Y} f (xs ∪X  ys) ≡ (SL-map {X} {Y} f xs) ∪Y (SL-map {X} {Y} f ys)
  SL-map-preserves-∪ {X} {Y} {f} xs ys = ≈L→≡ (proof Y) (FICM.extensionality (proof Y)
                                                                             (SL-map {X} {Y} f (xs ∪X  ys))
                                                                             ((SL-map {X} {Y} f xs) ∪Y (SL-map {X} {Y} f ys))
                                                                             (λ a → (λ p → FICM.∈∪-intro (proof Y) (lem1 a xs ys _ p) ) , lem2 a xs ys))
    where
      _∈X_ : Carrier X → SortedList (proof X) → Set
      _∈X_ = FICM._∈_ (proof X)

      _∈Y_ : Carrier Y → SortedList (proof Y) → Set
      _∈Y_ = FICM._∈_ (proof Y)

      _∪X_ : SortedList (proof X) → SortedList (proof X) → SortedList (proof X)
      _∪X_ = _∪_ (proof X)

      _∪Y_ : SortedList (proof Y) → SortedList (proof Y) → SortedList (proof Y)
      _∪Y_ = _∪_ (proof Y)

      unionX : (xs ys : SortedList (proof X)) → Acc _<N_ (length xs + length ys) → SortedList (proof X)
      unionX = union (proof X)

      mapf : SortedList (proof X) → SortedList (proof Y)
      mapf = SL-map {X} {Y} f

      compareX : Trichotomous _≡_ (_<_ X)
      compareX = IsStrictTotalOrder.compare (IsPropStrictTotalOrder.isSTO (proof X))


      lem1 : (a : Carrier Y) → (xs ys : SortedList (proof X))(p : Acc _<N_ (length xs + length ys)) →
             a ∈Y mapf (unionX xs ys p) → a ∈Y mapf xs ⊎ a ∈Y mapf ys
      lem1 a [] ys ac p = inj₂ p
      lem1 a (cons x xs x#xs) [] ac p = inj₁ p
      lem1 a (cons x xs x#xs) (cons y ys y#ys) (acc rs) p with compareX x y
      lem1 a (cons x xs x#xs) (cons y ys y#ys) (acc rs) p | tri< a₁ ¬b ¬c with FICM.∈union-elim (proof Y) {xs = cons (f x) [] []} {mapf (unionX xs (cons y ys y#ys) _)} _ p
      lem1 a (cons x xs x#xs) (cons y ys y#ys) (acc rs) p | tri< a₁ ¬b ¬c | inj₁ (here a=fx) = inj₁ (FICM.∈union-introˡ (proof Y) (here a=fx) (mapf xs) _ )
      lem1 a (cons x xs x#xs) (cons y ys y#ys) (acc rs) p | tri< a₁ ¬b ¬c | inj₂ a∈mapfxsyys with lem1 a xs (cons y ys y#ys) _ a∈mapfxsyys
      ... | inj₁ a∈mapfxs = inj₁ (FICM.∈union-introʳ (proof Y) (cons (f x) [] []) a∈mapfxs _)
      ... | inj₂ qq = inj₂ qq
      lem1 a (cons x xs x#xs) (cons y ys y#ys) (acc rs) p | tri≈ ¬a b ¬c with FICM.∈union-elim (proof Y) {xs = cons (f x) [] []} {mapf (unionX xs ys _)} _ p
      lem1 a (cons x xs x#xs) (cons y ys y#ys) (acc rs) p | tri≈ ¬a b ¬c | inj₁ (here a=fx) = inj₁ (FICM.∈union-introˡ (proof Y) (here a=fx) (mapf xs) _ )
      lem1 a (cons x xs x#xs) (cons y ys y#ys) (acc rs) p | tri≈ ¬a b ¬c | inj₂ a∈mapfxsys with lem1 a xs ys _ a∈mapfxsys
      ... | inj₁ a∈mapfxs = inj₁ (FICM.∈union-introʳ (proof Y) (cons (f x) [] []) a∈mapfxs _)
      ... | inj₂ a∈mapfys = inj₂ (FICM.∈union-introʳ (proof Y) (cons (f y) [] []) a∈mapfys _)
      lem1 a (cons x xs x#xs) (cons y ys y#ys) (acc rs) p | tri> ¬a ¬b c  with FICM.∈union-elim (proof Y) {xs = cons (f y) [] []} {mapf (unionX (cons x xs x#xs) ys _)} _ p
      lem1 a (cons x xs x#xs) (cons y ys y#ys) (acc rs) p | tri> ¬a ¬b c | inj₁ (here a=fy) = inj₂ (FICM.∈union-introˡ (proof Y) (here a=fy) (mapf ys) _ )
      lem1 a (cons x xs x#xs) (cons y ys y#ys) (acc rs) p | tri> ¬a ¬b c | inj₂ a∈mapfxxsys with lem1 a (cons x xs x#xs) ys _ a∈mapfxxsys
      ... | inj₁ qq = inj₁ qq
      ... | inj₂ a∈mapfys = inj₂ (FICM.∈union-introʳ (proof Y) (cons (f y) [] []) a∈mapfys _)

      lem2 : (a : Carrier Y) → (xs ys : SortedList (proof X)) →
             a ∈Y (mapf xs ∪Y mapf ys) → a ∈Y mapf (xs ∪X ys)
      lem2 a xs ys a∈mapfxs∪mapfys with FICM.∈∪-elim (proof Y) {xs = mapf xs} {mapf ys} a∈mapfxs∪mapfys
      ... | inj₁ a∈mapfxs = SL-map-preserves-⊆ f xs (xs ∪X ys) (λ b∈xs → FICM.∈∪-introˡ (proof X) b∈xs ys) a∈mapfxs
      ... | inj₂ a∈mapfys = SL-map-preserves-⊆ f ys (xs ∪X ys) (λ b∈ys → FICM.∈∪-introʳ (proof X) xs b∈ys) a∈mapfys


  SORTEDLIST : (ext : Extensionality _ _) → Functor STO (OICM ext)
  act (SORTEDLIST ext) (MkSto S _<_ sto) = MkOicm (SortedList sto) (FICM._<L_ sto) (_∪_ sto) [] (SL-isOICM sto)
  fmap (SORTEDLIST ext) {X} {Y} f = MkOicmMorphism (SL-map {X} {Y} f) refl SL-map-preserves-∪
  identity (SORTEDLIST ext) {X} = eqOicmMorphism ext (ext lem) where
    lem : ∀ (xs : SortedList (proof X)) → SL-map {X} {X} id xs ≡ xs
    lem [] = refl
    lem (cons x xs x#xs) = trans (cong (insert (proof X) x) (lem xs)) (FICM.insert-consview (proof X) x#xs)
  homomorphism (SORTEDLIST ext) {X} {Y} {Z} {f} {g} = eqOicmMorphism ext (ext lem) where
    lem : ∀ (xs : SortedList (proof X))
        → SL-map {X} {Z} (g ∘ f) xs
        ≡ (SL-map {Y} {Z} g ∘ SL-map {X} {Y} f) xs
    lem [] = refl
    lem (cons x xs fx) = trans (cong (_∪_ (proof Z) (cons (g (f x)) [] [])) (lem xs))
                               (sym (SL-map-preserves-∪ {f = g} (cons (f x) [] []) (SL-map f xs)))

-----------------------------------
-- The Free-Forgetful Adjunction --
-----------------------------------

  open Adjunction

  foldr-∙ : (A : PropStrictTotalOrder)
          → (B : OrderedIdempotentCommutativeMonoid)
          → (f : Carrier A → Carrier B)
          → SortedList (proof A) → Carrier B
  foldr-∙ A B f = foldr (λ a b → (_∙_ B) (f a) b) (ε B)

  foldr-∙-preserves-union : (A : PropStrictTotalOrder) (B : OrderedIdempotentCommutativeMonoid)
                    → (f : Carrier A → Carrier B)
                    → (xs ys : SortedList (proof A))
                    → (p : Acc _<N_ (length xs + length ys))
                    → foldr-∙ A B f (union (proof A) xs ys p)
                    ≡ (_∙_ B) (foldr-∙ A B f xs) (foldr-∙ A B f ys)
  foldr-∙-preserves-union A B f [] ys p = sym (identityˡ (isICM (proof B)) (foldr-∙ A B f ys))
  foldr-∙-preserves-union A B f (cons x xs x#xs) [] p = sym (trans (assoc (isICM (proof B)) (f x) (foldr-∙ A B f xs) (ε B))
                                                                   (cong (_∙_ B (f x)) (identityʳ (isICM (proof B)) (foldr-∙ A B f xs))))
  foldr-∙-preserves-union A B f (cons x xs x#xs) (cons y ys y#ys) (acc rs) with IsStrictTotalOrder.compare (IsPropStrictTotalOrder.isSTO (proof A)) x y
  ... | tri< _ _ _ = trans (cong (_∙_ B (f x)) (foldr-∙-preserves-union A B f xs (cons y ys y#ys) _))
                           (sym (assoc (isICM (proof B)) (f x) (foldr-∙ A B f xs) (foldr-∙ A B f (cons y ys y#ys))))
  ... | tri≈ _ refl _ = begin
    f x ∙B foldr-∙ A B f (unionA xs ys _)
      ≡⟨ cong (f x ∙B_) (foldr-∙-preserves-union A B f xs ys _) ⟩
    f x ∙B (foldr-∙ A B f xs ∙B foldr-∙ A B f ys)
      ≡⟨ cong (_∙B (foldr-∙ A B f xs ∙B foldr-∙ A B f ys)) (sym (idem (isICM (proof B)) (f x))) ⟩
    (f x ∙B f x) ∙B (foldr-∙ A B f xs ∙B foldr-∙ A B f ys)
      ≡⟨ trans (assoc (isICM (proof B)) (f x) (f x) (foldr-∙ A B f xs ∙B foldr-∙ A B f ys))
               (cong (f x ∙B_) (sym (assoc (isICM (proof B)) (f x) (foldr-∙ A B f xs) (foldr-∙ A B f ys)))) ⟩
    f x ∙B ((f x ∙B foldr-∙ A B f xs) ∙B foldr-∙ A B f ys)
      ≡⟨ cong (λ z → f x ∙B (z ∙B foldr-∙ A B f ys)) (comm (isICM (proof B)) (f x) (foldr-∙ A B f xs)) ⟩
    f x ∙B ((foldr-∙ A B f xs ∙B f x) ∙B foldr-∙ A B f ys)
      ≡⟨ trans (cong (f x ∙B_) (assoc (isICM (proof B)) (foldr-∙ A B f xs) (f x) (foldr-∙ A B f ys)))
               (sym (assoc (isICM (proof B)) (f x) (foldr-∙ A B f xs) (foldr-∙ A B f (cons y ys y#ys)))) ⟩
    (f x ∙B foldr-∙ A B f xs) ∙B (f x ∙B foldr-∙ A B f ys)
      ∎ where
          open ≡-Reasoning
          _∙B_ : Carrier B → Carrier B → Carrier B
          _∙B_ = _∙_ B

          unionA : (xs ys : SortedList (proof A)) → Acc _<N_ (length xs + length ys) → SortedList (proof A)
          unionA = union (proof A)
  ... | tri> _ _ _ = begin
    f y ∙B foldr-∙ A B f (unionA (cons x xs x#xs) ys _)
      ≡⟨ cong (f y ∙B_) (foldr-∙-preserves-union A B f (cons x xs x#xs) ys _) ⟩
    f y ∙B ((f x ∙B foldr-∙ A B f xs) ∙B foldr-∙ A B f ys)
      ≡⟨ trans (cong (f y ∙B_) (assoc (isICM (proof B)) (f x) (foldr-∙ A B f xs) (foldr-∙ A B f ys)))
               (sym (assoc (isICM (proof B)) (f y) (f x) (foldr-∙ A B f xs ∙B foldr-∙ A B f ys))) ⟩
    (f y ∙B f x) ∙B (foldr-∙ A B f xs ∙B foldr-∙ A B f ys)
      ≡⟨ cong (_∙B (foldr-∙ A B f xs ∙B foldr-∙ A B f ys)) (comm (isICM (proof B)) (f y) (f x)) ⟩
    (f x ∙B f y) ∙B (foldr-∙ A B f xs ∙B foldr-∙ A B f ys)
      ≡⟨ trans (assoc (isICM (proof B)) (f x) (f y) (foldr-∙ A B f xs ∙B foldr-∙ A B f ys))
               (cong (f x ∙B_) (sym (assoc (isICM (proof B)) (f y) (foldr-∙ A B f xs) (foldr-∙ A B f ys)))) ⟩
    f x ∙B ((f y ∙B foldr-∙ A B f xs) ∙B foldr-∙ A B f ys)
      ≡⟨ cong (λ z → f x ∙B (z ∙B foldr-∙ A B f ys)) (comm (isICM (proof B)) (f y) (foldr-∙ A B f xs)) ⟩
    f x ∙B ((foldr-∙ A B f xs ∙B f y) ∙B foldr-∙ A B f ys)
      ≡⟨ trans (cong (f x ∙B_) (assoc (isICM (proof B)) (foldr-∙ A B f xs) (f y) (foldr-∙ A B f ys)))
               (sym (assoc (isICM (proof B)) (f x) (foldr-∙ A B f xs) (f y ∙B foldr-∙ A B f ys))) ⟩
    (f x ∙B foldr-∙ A B f xs) ∙B (f y ∙B foldr-∙ A B f ys)
      ∎ where
          open ≡-Reasoning
          _∙B_ : Carrier B → Carrier B → Carrier B
          _∙B_ = _∙_ B

          unionA : (xs ys : SortedList (proof A)) → Acc _<N_ (length xs + length ys) → SortedList (proof A)
          unionA = union (proof A)

  foldr-∙-preserves-∪ : (A : PropStrictTotalOrder) (B : OrderedIdempotentCommutativeMonoid)
                    → (f : Carrier A → Carrier B)
                    → (xs ys : SortedList (proof A))
                    → foldr-∙ A B f (_∪_ (proof A) xs ys)
                    ≡ (_∙_ B) (foldr-∙ A B f xs) (foldr-∙ A B f ys)
  foldr-∙-preserves-∪ A B f xs ys = foldr-∙-preserves-union A B f xs ys _

  SL-Adjunction : (ext : Extensionality _ _) → (SORTEDLIST ext) ⊣ (FORGET ext)
  to (SL-Adjunction ext) f x = fun f (cons x [] [])

  fun (from (SL-Adjunction ext) {A} {B} f) = foldr-∙ A B f
  preserves-ε (from (SL-Adjunction ext) f) = refl
  preserves-∙ (from (SL-Adjunction ext) {A} {B} f) = foldr-∙-preserves-∪ A B f

  left-inverse-of (SL-Adjunction ext) {A} {B} f
    = eqOicmMorphism ext (ext (foldr-universal (fun f) (λ a → (_∙_ B) (fun f (cons a [] []))) (ε B)
                                           (preserves-ε f)
                                           λ x xs x#xs → trans (cong (fun f) (sym (FICM.insert-consview (proof A) x#xs) ))
                                                               (preserves-∙ f (cons x [] []) xs)))
  right-inverse-of (SL-Adjunction ext) {A} {B} f = ext λ x → (identityʳ $ isICM $ proof B) (f x)
  to-natural (SL-Adjunction ext) f g = ext (λ _ → ext (λ _ → refl))
