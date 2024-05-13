open import Algebra.Structures.Propositional

module Free.IdempotentCommutativeMonoid.Properties
  {X : Set} {_≈_ : X -> X -> Set} {_<_ : X -> X -> Set}
  (<-STO : IsPropStrictTotalOrder _≈_ _<_)
  where

open import Level renaming (suc to lsuc)
open import Algebra
open import Data.Product hiding (map)
open import Data.Sum hiding (map )
open import Data.Bool using (true; false)
open import Data.Unit
open import Data.Empty
open import Data.Nat hiding (_<?_; compare) renaming (_<_ to _<ℕ_)
open import Data.Nat.Properties hiding (<-trans; <-asym; <-irrefl; _<?_)
open import Data.Nat.Induction
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

open import Function
open import Induction.WellFounded

open import Relation.Binary hiding (NonEmpty; StrictTotalOrder)
open import Relation.Binary.Lattice
open import Relation.Binary.Isomorphism
open import Relation.Binary.PropositionalEquality hiding (isEquivalence)
open import Relation.Nullary hiding (Irrelevant)
open import Relation.Nullary.Decidable hiding (map)

open import Data.FreshList.InductiveInductive
open import Free.IdempotentCommutativeMonoid.Base <-STO



private
  -- Some more convenient names for the fields and subfields of the STO proof
  <-SPO    = IsPropStrictTotalOrder.isStrictPartialOrder <-STO
  ≈-Eq     = IsPropStrictTotalOrder.isEquivalence <-STO
  ≈-prop     = IsPropStrictTotalOrder.≈-prop <-STO
  <-prop     = IsPropStrictTotalOrder.<-prop <-STO
  <-trans  = IsPropStrictTotalOrder.trans <-STO
  <-irrefl = IsStrictPartialOrder.irrefl <-SPO
  <-asym   = IsStrictPartialOrder.asym <-SPO
  <-resp-≈ = IsStrictPartialOrder.<-resp-≈ <-SPO
  ≈-refl   = IsEquivalence.refl ≈-Eq
  ≈-sym    = IsEquivalence.sym ≈-Eq
  ≈-trans  = IsEquivalence.trans ≈-Eq
  _<?_     = IsPropStrictTotalOrder._<?_ <-STO
  _≈?_     = IsPropStrictTotalOrder._≟_ <-STO
  compare  = IsPropStrictTotalOrder.compare <-STO
  open import Relation.Unary.Finiteness (record {Carrier = X; _≈_ = _≈_; isEquivalence = ≈-Eq})

-- Since < is transitive, it suffices to know that z < head to cons z,
cons-head-< : ∀ {x y} {xs : SortedList} {fx : x # xs} -> y < x -> All (y <_) (cons x xs fx)
cons-head-< {fx = fx} y<x = y<x ∷ all-map (<-trans y<x) (fresh→all fx)

-- Overload for membership to work with  ≈
_∈_ : X -> SortedList -> Set
x ∈ xs = Any (x ≈_) xs

infix 10 _∈_

_∉_ : X -> SortedList -> Set
x ∉ xs = ¬ (Any (x ≈_) xs)

_⊆_ : (xs ys : SortedList) -> Set
xs ⊆ ys = ∀ {a} -> a ∈ xs -> a ∈ ys

_⊈_ : (xs ys : SortedList) -> Set
xs ⊈ ys = ¬ (xs ⊆ ys)

_∈?_ : Decidable _∈_
x ∈? xs = any? (x ≈?_) xs



#→∉ : ∀ {x} {xs : SortedList} -> x # xs -> x ∉ xs
#→∉ {x} {cons y ys fy} x#xs x∈xs with fresh→all {xs = cons y ys fy} x#xs
#→∉ {x} {cons y ys fy} x#xs (here x≈y) | x<y ∷ pxs = <-irrefl x≈y x<y
#→∉ {x} {cons y ys fy} x#xs (there x∈xs) | x<y ∷ pxs = #→∉ (all→fresh pxs) x∈xs


-- Equivalence preserves freshness
≈-preserves-# : ∀ {x y} {xs : SortedList} -> x # xs -> x ≈ y -> y # xs
≈-preserves-# = WithEq.#-resp-≈ _<_ ≈-Eq (IsPropStrictTotalOrder.<-resp-≈ <-STO)

-- Equivalence preserves membership
≈-preserves-∈ : ∀ {a b} {xs : SortedList} -> a ∈ xs -> a ≈ b -> b ∈ xs
≈-preserves-∈ (here a≈x) a≈b = here (≈-trans (≈-sym a≈b) a≈x)
≈-preserves-∈ (there a∈xs) a≈b = there (≈-preserves-∈ a∈xs a≈b)

-- If ≈ preserves ∈, then it also preserves ∉
≈-preserves-∉ : ∀ {x y} {xs : SortedList} -> x ∉ xs -> x ≈ y -> y ∉ xs
≈-preserves-∉ a∉xs a≈b (here b≈x) = a∉xs (here (≈-trans a≈b b≈x))
≈-preserves-∉ a∉xs a≈b (there b∈xs) = a∉xs (there (≈-preserves-∈ b∈xs (≈-sym a≈b)))

-- If the equivalence relation is propositional, then membership for sorted lists is propositional,
-- because an element can only appear once.
∈-irrelevant : ∀ {a} {xs : SortedList} -> (∀ {x y} -> (u v : x ≈ y) -> u ≡ v) -> (p q : a ∈ xs) -> p ≡ q
∈-irrelevant {a} {cons x xs fx} ≈-irrelevant (here p) (here q) = cong here (≈-irrelevant p q)
∈-irrelevant {a} {cons x xs fx} ≈-irrelevant (here p) (there q) = ⊥-elim (#→∉ fx (≈-preserves-∈ q p))
∈-irrelevant {a} {cons x xs fx} ≈-irrelevant (there p) (here q) = ⊥-elim (#→∉ fx (≈-preserves-∈ p q))
∈-irrelevant {a} {cons x xs fx} ≈-irrelevant (there p) (there q) = cong there (∈-irrelevant ≈-irrelevant p q)

all<-irrefl : ∀ {x} {xs : SortedList} -> x ∈ xs -> All (x <_) xs -> ⊥
all<-irrefl (here px)  (qx ∷ qxs) = <-irrefl px qx
all<-irrefl (there pxs) (qx ∷ qxs) = all<-irrefl pxs qxs

all>-irrefl : ∀ {x} {xs : SortedList} -> x ∈ xs -> All (_< x) xs -> ⊥
all>-irrefl (here px)  (qx ∷ qxs) = <-irrefl (≈-sym px) qx
all>-irrefl (there pxs) (qx ∷ qxs) = all>-irrefl pxs qxs

all<-resp-≈ : ∀ {x y} {xs : SortedList} -> x ≈ y -> All (x <_) xs -> All (y <_) xs
all<-resp-≈ x≈y [] = []
all<-resp-≈ x≈y (px ∷ pxs) = proj₂ <-resp-≈ x≈y px ∷ (all<-resp-≈ x≈y pxs)

all>-resp-≈ : ∀ {x y} {xs : SortedList} -> x ≈ y -> All (_< x) xs -> All (_< y) xs
all>-resp-≈ x≈y [] = []
all>-resp-≈ x≈y (px ∷ pxs) = proj₁ <-resp-≈ x≈y px ∷ (all>-resp-≈ x≈y pxs)



all>-trans : ∀ {x y} {xs : SortedList} -> All (_< x) xs -> x < y -> All (_< y) xs
all>-trans [] x<y = []
all>-trans (x<a ∷ pas) a<y = <-trans x<a a<y ∷ all>-trans pas a<y

all<-trans : ∀ {x y} {xs : SortedList} -> x < y -> All (y <_) xs -> All (x <_) xs
all<-trans x<y [] = []
all<-trans x<y (y<a ∷ pas) = <-trans x<y y<a ∷ all<-trans x<y pas

---------------------------------
-- Equivalence of Sorted Lists --
---------------------------------

-- We lift ≈ pointwise
data _≈L_ : SortedList -> SortedList -> Set where
  [] : [] ≈L []
  cons : {x y : X} {xs ys : SortedList} {fx : x # xs} {fy : y # ys}
       -> x ≈ y -> xs ≈L ys -> (cons x xs fx) ≈L (cons y ys fy)

≈L-refl : { xs : SortedList } -> xs ≈L xs
≈L-refl {[]} = []
≈L-refl {cons x xs fx} = cons ≈-refl ≈L-refl

≈L-sym : {xs ys : SortedList} -> xs ≈L ys -> ys ≈L xs
≈L-sym [] = []
≈L-sym (cons x p) = cons (≈-sym x) (≈L-sym p)

≈L-trans : {xs ys zs : SortedList} -> xs ≈L ys -> ys ≈L zs -> xs ≈L zs
≈L-trans [] q = q
≈L-trans (cons x p) (cons y q) = cons (≈-trans x y) (≈L-trans p q)

≈L-prop : Irrelevant (_≈L_)
≈L-prop [] [] = refl
≈L-prop (cons x=y xs=ys) (cons x=y' xs=ys') = cong₂ cons (IsPropStrictTotalOrder.≈-prop <-STO x=y x=y') (≈L-prop xs=ys xs=ys')

isEquivalence : IsEquivalence _≈L_
IsEquivalence.refl isEquivalence = ≈L-refl
IsEquivalence.sym isEquivalence = ≈L-sym
IsEquivalence.trans isEquivalence = ≈L-trans

_≈?L_ : Decidable _≈L_
[] ≈?L [] = yes []
[] ≈?L cons y ys fy = no λ ()
cons x xs fx ≈?L [] = no λ ()
cons x xs fx ≈?L cons y ys fy with x ≈? y | xs ≈?L ys
... | yes p | yes q = yes (cons p q)
... | no ¬p | _ = no λ { (cons p q) → ¬p p}
... | _ | no ¬q = no λ { (cons p q) → ¬q q}

≡→≈L : {xs ys : SortedList} -> xs ≡ ys -> xs ≈L ys
≡→≈L refl = ≈L-refl

module ≈L-Reasoning where
  infix  3 _∎
  infixr 2 _≈⟨⟩_ step-≈ step-≈˘
  infix  1 begin_

  begin_ : {x y : SortedList} → x ≈L y → x ≈L y
  begin_ x≈y = x≈y

  _≈⟨⟩_ : ∀ (x {y} : SortedList) → x ≈L y → x ≈L y
  _ ≈⟨⟩ x≈y = x≈y

  step-≈ : ∀ (x {y z} : SortedList) → y ≈L z → x ≈L y → x ≈L z
  step-≈ _ y≈z x≈y = ≈L-trans x≈y y≈z

  step-≈˘ : ∀ (x {y z} : SortedList) → y ≈L z → y ≈L x → x ≈L z
  step-≈˘ _ y≈z y≈x = ≈L-trans (≈L-sym y≈x) y≈z

  _∎ : ∀ (x : SortedList) → x ≈L x
  _∎ _ = ≈L-refl

  syntax step-≈  x y≈z x≈y = x ≈⟨  x≈y ⟩ y≈z
  syntax step-≈˘ x y≈z y≈x = x ≈˘⟨ y≈x ⟩ y≈z

nil≉cons : {x : X} {xs : SortedList} {x#xs : x # xs} → ¬ ([] ≈L cons x xs x#xs)
nil≉cons ()


----------------------
-- Properties of ≈L --
----------------------

∈-preserves-≈L : ∀ {a} {xs ys : SortedList} -> a ∈ xs -> xs ≈L ys -> a ∈ ys
∈-preserves-≈L (here a≈x) (cons x≈y xs≈ys) = here (≈-trans a≈x x≈y)
∈-preserves-≈L (there a∈xs) (cons x≈y xs≈ys) = there (∈-preserves-≈L a∈xs xs≈ys)

∉-preserves-≈L : ∀ {a} {xs ys : SortedList} -> a ∉ xs -> xs ≈L ys -> a ∉ ys
∉-preserves-≈L a∉xs xs≈ys a∈ys = a∉xs (∈-preserves-≈L a∈ys (≈L-sym xs≈ys))

≈L-preserves-length : {xs ys : SortedList} -> xs ≈L ys -> length xs ≡ length ys
≈L-preserves-length [] = refl
≈L-preserves-length (cons x≈y xs≈ys) = cong suc (≈L-preserves-length xs≈ys)

------------------------------
-- Properties of All and ≈L --
------------------------------

-- If P respects ≈, then All P respects ≈ and ≈L
all-resp-≈L : ∀ {xs ys : SortedList} {P : X -> Set}
            → (∀ {a b} → a ≈ b → P a → P b) --todo: this almost definitely has a name
            → xs ≈L ys
            → All P xs → All P ys
all-resp-≈L f [] pxs = pxs
all-resp-≈L f (cons x≈y xs≈ys) (px ∷ pxs) = f x≈y px ∷ all-resp-≈L f xs≈ys pxs

-------------------------------
-- SortedList Extensionality --
-------------------------------

-- Something which is smaller than the head cannot appear elsewhere in the list.
ext-lem : {a x : X} {xs : SortedList} {fx : x # xs} -> a < x -> a ∉ (cons x xs fx)
ext-lem a<x (here a≈x) = <-irrefl a≈x a<x
ext-lem {a} {x} {xs} {fx} a<x (there a∈xs) with fresh→all fx
... | px ∷ pxs = ext-lem (<-trans a<x px) a∈xs

-- Two sorted lists with the same elements are the same list.
extensionality : (xs ys : SortedList)
                       -> (∀ x -> ((x ∈ xs) -> (x ∈ ys)) × ((x ∈ ys) -> (x ∈ xs)))
                       -> xs ≈L ys
extensionality [] [] p = []
extensionality [] (cons x xs fx) p with (proj₂ (p x)) (here ≈-refl)
... | ()
extensionality (cons x xs fx) [] p with (proj₁ (p x)) (here ≈-refl)
... | ()
extensionality (cons x xs fx) (cons y ys fy) p with compare x y
... | tri≈ ¬lt x≈y ¬gt = cons x≈y (extensionality xs ys (λ z → f z , g z)) where
  f : ∀ z -> z ∈ xs -> z ∈ ys
  f z z∈xs with proj₁ (p z) (there z∈xs)
  ... | here z≈y = ⊥-elim (all<-irrefl z∈xs (fresh→all (≈-preserves-# fx (≈-trans x≈y (≈-sym z≈y)))))
  ... | there z∈ys = z∈ys

  g : ∀ z -> z ∈ ys -> z ∈ xs
  g z z∈ys with proj₂ (p z) (there z∈ys)
  ... | here z≈x = ⊥-elim (all<-irrefl z∈ys (fresh→all (≈-preserves-# fy (≈-trans (≈-sym x≈y) (≈-sym z≈x)))))
  ... | there z∈xs = z∈xs
... | tri< lt ¬eq ¬gt = ⊥-elim (ext-lem (lt) (proj₁ (p x) (here ≈-refl)))
... | tri> ¬lt ¬eq gt = ⊥-elim (ext-lem (gt) (proj₂ (p y) (here ≈-refl)))


-----------------------
-- Length Properties --
-----------------------

weaken-∉ : ∀ {x a} {as : SortedList} {fa : a # as} -> x ∉ (cons a as fa) -> x ∉ as
weaken-∉ x (here x₁) = x (there (here x₁))
weaken-∉ x (there x₁) = x (there (there x₁))

strengthen-∉ : ∀ {x a} {as : SortedList} {fa : a # as} -> ¬ (x ≈ a) -> x ∉ as -> x ∉ (cons a as fa)
strengthen-∉ x≉a x∉as (here x≈a) = x≉a x≈a
strengthen-∉ x≉a x∉as (there x∈as) = x∉as x∈as

----------------------
-- Union Properties --
----------------------

opaque
  unfolding union

  ∈union-elim : ∀ {a} {xs ys : SortedList} -> (p : Acc _<ℕ_ (length xs + length ys)) → a ∈ (union xs ys p) -> a ∈ xs ⊎ a ∈ ys
  ∈union-elim {a} {[]} {ys} p a∈ys = inj₂ a∈ys
  ∈union-elim {a} {cons x xs x#xs} {[]} p a∈xs = inj₁ a∈xs
  ∈union-elim {a} {cons x xs x#xs} {cons y ys y#ys} (acc rs) a∈xs∪ys with compare x y
  ∈union-elim {a} {cons x xs x#xs} {cons y ys y#ys} (acc rs) (here a≈x) | tri< x<y ¬x≈y ¬y<x = inj₁ (here a≈x)
  ∈union-elim {a} {cons x xs x#xs} {cons y ys y#ys} (acc rs) (there a∈xs∪yys) | tri< x<y ¬x≈y ¬y<x with ∈union-elim {a} {xs} {cons y ys y#ys} _ a∈xs∪yys
  ... | inj₁ a∈xs = inj₁ (there a∈xs)
  ... | inj₂ a∈yys = inj₂ a∈yys
  ∈union-elim {a} {cons x xs x#xs} {cons y ys y#ys} (acc rs) (here a≈x) | tri≈ ¬x<y x≈y ¬y<x = inj₁ (here a≈x)
  ∈union-elim {a} {cons x xs x#xs} {cons y ys y#ys} (acc rs) (there a∈xs∪ys) | tri≈ ¬x<y x≈y ¬y<x with ∈union-elim {a} {xs} {ys} _ a∈xs∪ys
  ... | inj₁ a∈xs = inj₁ (there a∈xs)
  ... | inj₂ a∈ys = inj₂ (there a∈ys)
  ∈union-elim {a} {cons x xs x#xs} {cons y ys y#ys} (acc rs) (here a≈y) | tri> ¬x<y ¬x≈y y<x = inj₂ (here a≈y)
  ∈union-elim {a} {cons x xs x#xs} {cons y ys y#ys} (acc rs) (there a∈xxs∪ys) | tri> ¬x<y ¬x≈y y<x with ∈union-elim {a} {cons x xs x#xs} {ys} _ a∈xxs∪ys
  ... | inj₁ a∈xxs = inj₁ a∈xxs
  ... | inj₂ a∈ys = inj₂ (there a∈ys)

  ∈∪-elim : ∀ {a} {xs ys : SortedList} -> a ∈ (xs ∪ ys) -> a ∈ xs ⊎ a ∈ ys
  ∈∪-elim {a} {xs} {ys} = ∈union-elim (<-wellFounded (length xs + length ys))

  ∉∪-intro : ∀ {a} {xs ys : SortedList} -> a ∉ xs -> a ∉ ys -> a ∉ (xs ∪ ys)
  ∉∪-intro {a} {[]} {ys} a∉xs a∉ys = a∉ys
  ∉∪-intro {a} {cons x xs fx} {ys} a∉xs a∉ys a∈∪ with ∈∪-elim a∈∪
  ... | inj₁ a∈xs = a∉xs a∈xs
  ... | inj₂ a∈ys = a∉ys a∈ys


  ∈union-introˡ : ∀ {a} {xs : SortedList} -> a ∈ xs -> (ys : SortedList) -> (p : Acc _<ℕ_ (length xs + length ys)) -> a ∈ (union xs ys p)
  ∈union-introˡ {a} {cons x xs x#xs} (here a≈x) [] p = here a≈x
  ∈union-introˡ {a} {cons x xs x#xs} (here a≈x) (cons y ys y#ys) (acc rs) with compare x y
  ... | tri< _ _ _ = here a≈x
  ... | tri≈ _ _ _ = here a≈x
  ... | tri> _ _ _ = there (∈union-introˡ {a} {cons x xs x#xs} (here a≈x) ys _)
  ∈union-introˡ {a} {cons x xs x#xs} (there a∈xs) [] p = there a∈xs
  ∈union-introˡ {a} {cons x xs x#xs} (there a∈xs) (cons y ys y#ys) (acc rs) with compare x y
  ... | tri< _ _ _ = there (∈union-introˡ {a} {xs} a∈xs (cons y ys y#ys) _)
  ... | tri≈ _ _ _ = there (∈union-introˡ {a} {xs} a∈xs ys _)
  ... | tri> _ _ _ = there (∈union-introˡ {a} {cons x xs x#xs} (there a∈xs) ys _)

  ∈union-introʳ : ∀ {a} {ys : SortedList} -> (xs : SortedList) → a ∈ ys -> (p : Acc _<ℕ_ (length xs + length ys)) -> a ∈ (union xs ys p)
  ∈union-introʳ {a} {ys} [] a∈ys p = a∈ys
  ∈union-introʳ {a} {cons y ys y#ys} (cons x xs x#xs) a∈yys (acc rs) with compare x y
  ... | tri< _ _ _ = there (∈union-introʳ {a} {cons y ys y#ys} xs a∈yys _)
  ∈union-introʳ {a} {cons y ys y#ys} (cons x xs x#xs) (here a≈y) (acc rs) | tri≈ _ x≈y _ = here (≈-trans a≈y (≈-sym x≈y))
  ∈union-introʳ {a} {cons y ys y#ys} (cons x xs x#xs) (there a∈ys) (acc rs) | tri≈ _ _ _ = there (∈union-introʳ {a} {ys} xs a∈ys _)
  ∈union-introʳ {a} {cons y ys y#ys} (cons x xs x#xs) (here a≈y) (acc rs) | tri> _ _ _ = here a≈y
  ∈union-introʳ {a} {cons y ys y#ys} (cons x xs x#xs) (there a∈ys) (acc rs) | tri> _ _ _ = there (∈union-introʳ {a} {ys} (cons x xs x#xs) a∈ys _)

  ∈∪-introˡ : ∀ {a} {xs : SortedList} -> a ∈ xs -> (ys : SortedList) -> a ∈ (xs ∪ ys)
  ∈∪-introˡ {a} {xs} a∈xs ys = ∈union-introˡ a∈xs ys (<-wellFounded (length xs + length ys))

  ∈∪-introʳ : ∀ {x} {ys : SortedList} -> (xs : SortedList) -> x ∈ ys -> x ∈ (xs ∪ ys)
  ∈∪-introʳ {a} {ys} xs a∈ys = ∈union-introʳ {a} {ys} xs a∈ys (<-wellFounded (length xs + length ys))

  ∈∪-intro : ∀ {a} {xs ys : SortedList} -> (a ∈ xs) ⊎ (a ∈ ys) → a ∈ (xs ∪ ys)
  ∈∪-intro {xs = xs} {ys} (inj₁ a∈xs) = ∈∪-introˡ a∈xs ys
  ∈∪-intro {xs = xs} {ys} (inj₂ a∈ys) = ∈∪-introʳ xs a∈ys

  ∉∪-introˡ : ∀ {a} {xs ys : SortedList} -> a ∉ (xs ∪ ys) -> a ∉ xs
  ∉∪-introˡ {ys = ys} ¬p a∈xs = ¬p (∈∪-introˡ a∈xs ys)

  ∉∪-introʳ : ∀ {a} {xs ys : SortedList} -> a ∉ (xs ∪ ys) -> a ∉ ys
  ∉∪-introʳ {xs = xs} ¬p a∈ys = ¬p (∈∪-introʳ xs a∈ys)

  ∪-idʳ : (xs : SortedList) -> (xs ∪ []) ≡ xs
  ∪-idʳ [] = refl
  ∪-idʳ (cons x xs fx) rewrite ∪-idʳ xs = refl

  ∪-id : Identity _≈L_ [] _∪_
  proj₁ ∪-id = λ x → ≈L-refl
  proj₂ ∪-id = λ x → ≡→≈L (∪-idʳ x)

∪-comm : ( xs ys : SortedList ) -> (xs ∪ ys) ≈L (ys ∪ xs)
∪-comm xs ys = extensionality (xs ∪ ys) (ys ∪ xs) (λ x → f xs ys x , f ys xs x)
  where
    f : (xs ys : SortedList) → (x : X) → x ∈ (xs ∪ ys) → x ∈ (ys ∪ xs)
    f xs ys x x∈xs∪ys with ∈∪-elim x∈xs∪ys
    ... | inj₁ x∈xs = ∈∪-introʳ ys x∈xs
    ... | inj₂ x∈ys = ∈∪-introˡ x∈ys xs

∪-idempotent : Idempotent _≈L_ _∪_
∪-idempotent xs = extensionality (xs ∪ xs) xs (λ x → (λ x∈xs∪xs → [ id , id ]′ (∈∪-elim x∈xs∪xs) ) , ∈∪-introʳ xs)

∪-preserves-≈L : {xs xs' ys ys' : SortedList} -> xs ≈L xs' -> ys ≈L ys' -> (xs ∪ ys) ≈L (xs' ∪ ys')
∪-preserves-≈L {xs} {xs'} {ys} {ys'} xs=xs' ys=ys' = extensionality _ _ λ x → f x xs=xs' ys=ys' , f x (≈L-sym xs=xs') (≈L-sym ys=ys')
  where
    f : (x : X) → {xs xs' ys ys' : SortedList} -> xs ≈L xs' -> ys ≈L ys' → x ∈ (xs ∪ ys) → x ∈ (xs' ∪ ys')
    f x {xs} {xs'} {ys} {ys'} xs=xs' ys=ys' x∈xs∪xs = [ (λ x∈xs → ∈∪-introˡ (∈-preserves-≈L x∈xs xs=xs') ys') , (λ x∈ys → ∈∪-introʳ xs' (∈-preserves-≈L x∈ys ys=ys')) ]′ (∈∪-elim x∈xs∪xs)

∪-cancelˡ : {xs ys : SortedList} -> xs ≈L ys -> (xs ∪ ys) ≈L xs
∪-cancelˡ {xs} {ys} xs=ys = begin
  xs ∪ ys
    ≈⟨ ∪-preserves-≈L (≈L-refl {xs}) (≈L-sym xs=ys) ⟩
  xs ∪ xs
    ≈⟨ ∪-idempotent xs ⟩
  xs
    ∎ where open ≈L-Reasoning

∪-assoc : (xs ys zs : SortedList) -> ((xs ∪ ys) ∪ zs) ≈L (xs ∪ (ys ∪ zs))
∪-assoc xs ys zs = extensionality ((xs ∪ ys) ∪ zs) (xs ∪ (ys ∪ zs)) (λ x → f x , g x)
  where
    f : (x : X) → (x ∈ ((xs ∪ ys) ∪ zs) → x ∈ (xs ∪ (ys ∪ zs)))
    f x x∈xs∪ys∪zs with ∈∪-elim {xs = xs ∪ ys} x∈xs∪ys∪zs
    f x x∈xs∪ys∪zs | inj₁ x∈xs∪ys with ∈∪-elim {xs = xs} x∈xs∪ys
    ... | inj₁ x∈xs = ∈∪-introˡ x∈xs (ys ∪ zs)
    ... | inj₂ x∈ys = ∈∪-introʳ xs (∈∪-introˡ x∈ys zs)
    f x x∈xs∪ys∪zs | inj₂ x∈zs = ∈∪-introʳ xs (∈∪-introʳ ys x∈zs)

    g : (x : X) → (x ∈ (xs ∪ (ys ∪ zs)) → x ∈ ((xs ∪ ys) ∪ zs))
    g x x∈xs∪ys∪zs with ∈∪-elim {xs = xs} x∈xs∪ys∪zs
    g x x∈xs∪ys∪zs | inj₁ x∈xs = ∈∪-introˡ (∈∪-introˡ x∈xs ys) zs
    g x x∈xs∪ys∪zs | inj₂ x∈ys∪zs with ∈∪-elim {xs = ys} x∈ys∪zs
    ... | inj₁ x∈ys = ∈∪-introˡ (∈∪-introʳ xs x∈ys) zs
    ... | inj₂ x∈zs = ∈∪-introʳ (xs ∪ ys) x∈zs

-----------------------
-- Insert Properties --
-----------------------

opaque
  unfolding union

  insert-consview : ∀ {x} {xs : SortedList} → (fx : x # xs) → insert x xs ≡ cons x xs fx
  insert-consview {xs = []} [] = refl
  insert-consview {x} {xs = cons y ys y#ys} x#xs with compare x y
  ... | tri< _ _ _ = WithIrr.cons-cong _<_ (IsPropStrictTotalOrder.<-prop <-STO) refl refl
  insert-consview {x} {cons y ys y#ys} (x<y ∷ x#xs) | tri≈ _ x≈y _ = ⊥-elim (<-irrefl x≈y x<y)
  insert-consview {x} {cons y ys y#ys} (x<y ∷ x#ys) | tri> _ _ y<x = ⊥-elim (<-irrefl (≈-refl {x}) (<-trans x<y y<x))

∈insert-introˡ' : {a x : X} {xs : SortedList} → a ≈ x → a ∈ (insert x xs)
∈insert-introˡ' {xs = xs} p = ∈∪-introˡ (here p) xs

∈insert-introˡ : (x : X) (xs : SortedList) → x ∈ (insert x xs)
∈insert-introˡ x xs = ∈∪-introˡ (here ≈-refl) xs

∈insert-introʳ : {a x : X} {xs : SortedList} → a ∈ xs → a ∈ (insert x xs)
∈insert-introʳ {x = x} = ∈∪-introʳ (cons x [] [])

∈insert-elim : {a x : X} {xs : SortedList} → a ∈ (insert x xs) → a ≈ x ⊎ a ∈ xs
∈insert-elim {a} {x} {xs} p with ∈∪-elim {a} {cons x [] []} {xs} p
... | inj₁ (here p) = inj₁ p
... | inj₂ p = inj₂ p

insert-preserves-≈L : {x y : X} {xs ys : SortedList} → x ≈ y → xs ≈L ys → insert x xs ≈L insert y ys
insert-preserves-≈L p q = ∪-preserves-≈L (cons p []) q

insert-comm : ∀ x y xs → insert x (insert y xs) ≈L insert y (insert x xs)
insert-comm x y xs = ≈L-trans (≈L-sym (∪-assoc (cons x [] []) (cons y [] []) xs)) (≈L-trans (∪-preserves-≈L (∪-comm (cons x [] []) (cons y [] [])) ≈L-refl) (∪-assoc (cons y [] []) (cons x [] []) xs))

insert-idempotent : ∀ y x xs → x ≡ y → insert y (insert x xs) ≈L insert x xs
insert-idempotent x .x xs refl = ≈L-trans (≈L-sym $ ∪-assoc (cons x [] []) (cons x [] []) xs) (∪-preserves-≈L {ys = xs} (∪-idempotent (cons x [] [])) ≈L-refl)

insert-idempotent' : ∀ y x xs → x ≡ y → insert y (insert x xs) ≈L insert y xs
insert-idempotent' x .x xs refl = insert-idempotent x x xs refl

-------------------------------
-- Insertion Sort Properties --
-------------------------------

module _ where
  private
    open import Data.List as L
    open import Data.List.Membership.Setoid as L using ()
    open import Data.List.Relation.Unary.Any as L using ()
    _∈'_ = L._∈_ (record { Carrier = X ; _≈_ = _≈_ ; isEquivalence = ≈-Eq })
    _∉'_ = L._∉_ (record { Carrier = X ; _≈_ = _≈_ ; isEquivalence = ≈-Eq })

  insertion-sort-preserves-∈ : {a : X} {xs : List X} → a ∈' xs → a ∈ (insertion-sort xs)
  insertion-sort-preserves-∈ {a} {x ∷ xs} (L.here p) = ∈insert-introˡ' {a} {x} {insertion-sort xs} p
  insertion-sort-preserves-∈ {a} {x ∷ xs} (L.there p) = ∈insert-introʳ {a} {x} (insertion-sort-preserves-∈ p)

  insertion-sort-preserves-∈-inverse : {a : X} {xs : List X} → a ∈ (insertion-sort xs) → a ∈' xs
  insertion-sort-preserves-∈-inverse {a} {x ∷ xs} p with ∈insert-elim {a} {x} {insertion-sort xs} p
  ... | inj₁ q = L.here q
  ... | inj₂ q = L.there (insertion-sort-preserves-∈-inverse q)

  insertion-sort-preserves-∉ : {a : X} {xs : List X} → a ∉' xs → a ∉ (insertion-sort xs)
  insertion-sort-preserves-∉ {a} {x ∷ xs} ¬p q with ∈insert-elim {a} {x} {insertion-sort xs} q
  ... | inj₁ r = ¬p (L.here r)
  ... | inj₂ r = ¬p (L.there (insertion-sort-preserves-∈-inverse r))


----------------------------
-- Lexicographic Ordering --
----------------------------

-- lexicographic strict less-than relation on lists
data _<-lex_ : SortedList → SortedList → Set where
  [] : ∀ {x xs fx} → [] <-lex (cons x xs fx)
  here : ∀ {x xs fx y ys fy} → x < y → (cons x xs fx) <-lex (cons y ys fy)
  there : ∀ {x xs fx y ys fy} → x ≈ y → xs <-lex ys → (cons x xs fx) <-lex (cons y ys fy)

<-lex-trans : ∀ {xs ys zs} → xs <-lex ys → ys <-lex zs → xs <-lex zs
<-lex-trans [] (here y<z) = []
<-lex-trans [] (there y≈z ys<zs) = []
<-lex-trans (here x<y) (here y<z) = here (<-trans x<y y<z)
<-lex-trans (here x<y) (there y≈z ys<zs) = here (proj₁ <-resp-≈ y≈z x<y)
<-lex-trans (there x≈y xs<ys) (here y<z) = here (proj₂ <-resp-≈ (≈-sym x≈y) y<z  )
<-lex-trans (there x≈y xs<ys) (there y≈z ys<zs) = there (≈-trans x≈y y≈z) (<-lex-trans xs<ys ys<zs)

compareL : Trichotomous _≈L_ _<-lex_
compareL [] [] = tri≈ (λ {()}) [] (λ {()})
compareL [] (cons y ys fy) = tri< [] (λ {()}) λ {()}
compareL (cons x xs fx) [] = tri> (λ {()}) (λ {()}) []
compareL (cons x xs fx) (cons y ys fy) with compare x y
... | tri< x<y x≉y x≯y = tri< (here x<y) (λ {(cons x≈y _) → x≉y x≈y }) λ { (here x>y) → x≯y x>y ; (there y≈x _) → x≉y (≈-sym y≈x)}
... | tri> x≮y x≉y x>y = tri> (λ { (here x<y) → x≮y x<y ; (there x≈y _) → x≉y x≈y}) (λ { (cons x≈y _) → x≉y x≈y}) (here x>y)
... | tri≈ x≮y x≈y x≯y with compareL xs ys
... | tri< xs<ys xs≉ys xs≯ys = tri< (there x≈y xs<ys) (λ { (cons _ xs≈ys) → xs≉ys xs≈ys}) λ { (here y<x) → x≯y y<x ; (there _ ys<xs) → xs≯ys ys<xs}
... | tri≈ xs≮ys xs≈ys xs≯ys = tri≈ (λ { (here x<y) → x≮y x<y ; (there _ xs<ys) → xs≮ys xs<ys}) (cons x≈y xs≈ys) λ { (here y<x) → x≯y y<x ; (there _ ys<xs) → xs≯ys ys<xs}
... | tri> xs≮ys xs≉ys xs>ys = tri> (λ { (here x<y) → x≮y x<y ; (there _ xs<ys) → xs≮ys xs<ys}) (λ { (cons _ xs≈ys) → xs≉ys xs≈ys}) (there (≈-sym x≈y) xs>ys)

<L-prop : Irrelevant _<-lex_
<L-prop [] [] = refl
<L-prop (here x<y) (here x<y') = cong here (IsPropStrictTotalOrder.<-prop <-STO x<y x<y')
<L-prop (here x<y) (there x=y xs<ys) = ⊥-elim (<-irrefl x=y x<y)
<L-prop (there x=y xs<ys) (here x<y) = ⊥-elim (<-irrefl x=y x<y)
<L-prop (there x=y xs<ys) (there x=y' xs<ys') = cong₂ there (IsPropStrictTotalOrder.≈-prop <-STO x=y x=y') (<L-prop xs<ys xs<ys')

-- <-lex-STO : IsPropStrictTotalOrder _≈L_ _<-lex_
-- IsStrictTotalOrder.isEquivalence (IsPropStrictTotalOrder.isSTO <-lex-STO) = isEquivalence
-- IsStrictTotalOrder.trans (IsPropStrictTotalOrder.isSTO <-lex-STO) = <-lex-trans
-- IsStrictTotalOrder.compare (IsPropStrictTotalOrder.isSTO <-lex-STO) = compareL
-- IsPropStrictTotalOrder.≈-prop <-lex-STO = ≈L-prop
-- IsPropStrictTotalOrder.<-prop <-lex-STO = <L-prop

-- <L-trans = <-lex-trans
-- _<L_ = _<-lex_
-- <L-STO = <-lex-STO

-----------------------------------
-- Idempotent Commutative Monoid --
-----------------------------------

isSemigroup : IsSemigroup _≈L_ _∪_
IsMagma.isEquivalence (IsSemigroup.isMagma isSemigroup) = isEquivalence
IsMagma.∙-cong (IsSemigroup.isMagma isSemigroup) = ∪-preserves-≈L
IsSemigroup.assoc isSemigroup = ∪-assoc

isMonoid : IsMonoid _≈L_ _∪_ []
IsMonoid.isSemigroup isMonoid = isSemigroup
IsMonoid.identity isMonoid = ∪-id

isCommMonoid : IsCommutativeMonoid _≈L_ _∪_ []
IsCommutativeMonoid.isMonoid isCommMonoid = isMonoid
IsCommutativeMonoid.comm isCommMonoid = ∪-comm

isIdemCommMonoid : IsIdempotentCommutativeMonoid _≈L_ _∪_ []
IsIdempotentCommutativeMonoid.isCommutativeMonoid isIdemCommMonoid = isCommMonoid
IsIdempotentCommutativeMonoid.idem isIdemCommMonoid = ∪-idempotent

-- isOICM : IsOrderedIdempotentCommutativeMonoid _≈L_ _<-lex_ _∪_ []
-- IsOrderedIdempotentCommutativeMonoid.isICM isOICM = isIdemCommMonoid
-- IsOrderedIdempotentCommutativeMonoid.isSTO isOICM = <-lex-STO


-----------------------
-- Properties of _∩_ --
-----------------------

-- Left elimination principle for membership in an intersection
∈∩-elimˡ : {a : X} {xs ys : SortedList} → a ∈ (xs ∩ ys) → a ∈ xs
∈∩-elimˡ {a} {cons x xs x#xs} {ys} p with any? (x ≈?_) ys
... | no ¬q = there $ ∈∩-elimˡ {a} {xs} {ys} p
... | yes q with ∈insert-elim {a} {x} {xs ∩ ys} p
... | inj₁ r = here r
... | inj₂ r = there $ ∈∩-elimˡ {a} {xs} {ys} r

-- Right elimination principle for membership in an intersection
∈∩-elimʳ : {a : X} (xs : SortedList) {ys : SortedList} → a ∈ (xs ∩ ys) → a ∈ ys
∈∩-elimʳ {a} (cons x xs x#xs) {ys} p with any? (x ≈?_) ys
... | no ¬q = ∈∩-elimʳ {a} xs p
... | yes q with ∈insert-elim {a} {x} {xs ∩ ys} p
... | inj₁ r = ≈-preserves-∈ q (≈-sym r)
... | inj₂ r = ∈∩-elimʳ {a} xs r

∈∩-elim : {a : X} (xs ys : SortedList) → a ∈ (xs ∩ ys) → a ∈ xs × a ∈ ys
∈∩-elim {a} xs ys p = ∈∩-elimˡ p , ∈∩-elimʳ xs p

-- Introduction principle for membership in an intersection
∈∩-intro : {a : X} {xs ys : SortedList} → a ∈ xs → a ∈ ys → a ∈ (xs ∩ ys)
∈∩-intro {a} {cons x xs x#xs} {ys} p q with any? (x ≈?_) ys
∈∩-intro {a} {cons x xs x#xs} {ys} (here a≈x) q | yes u = ∈insert-introˡ' {xs = xs ∩ ys} a≈x
∈∩-intro {a} {cons x xs x#xs} {ys} (there p) q | yes u = ∈insert-introʳ (∈∩-intro p q)
∈∩-intro {a} {cons x xs x#xs} {ys} (here a≈x) q | no ¬u = ⊥-elim (¬u (≈-preserves-∈ q a≈x))
∈∩-intro {a} {cons x xs x#xs} {ys} (there p) q | no ¬u = ∈∩-intro p q

-- Right introduction principle for non-membership in an intersection
∉∩-introʳ : {a : X} {xs ys : SortedList} → a ∉ ys → a ∉ (xs ∩ ys)
∉∩-introʳ {a} {xs} {ys} ¬p q = ¬p $ ∈∩-elimʳ xs q

-- Left introduction principle for non-membership in an intersection
∉∩-introˡ : {a : X} {xs ys : SortedList} → a ∉ xs → a ∉ (xs ∩ ys)
∉∩-introˡ {a} {xs} {ys} ¬p q = ¬p $ ∈∩-elimˡ q

-- Elimination principle for non-membership in an intersection
∉∩-elim : {a : X} {xs ys : SortedList} → a ∉ (xs ∩ ys) → (a ∉ xs) ⊎ (a ∉ ys)
∉∩-elim {a} {xs} {ys} ¬p with a ∈? xs
... | no a∉xs = inj₁ a∉xs
... | yes a∈xs with a ∈? ys
... | no a∉ys = inj₂ a∉ys
... | yes a∈ys = ⊥-elim $ ¬p (∈∩-intro a∈xs a∈ys)

∩-assoc : Associative _≈L_ _∩_
∩-assoc xs ys zs = extensionality _ _ λ x → f x , g x where
  f : (a : X) → a ∈ ((xs ∩ ys) ∩ zs) → a ∈ (xs ∩ (ys ∩ zs))
  f a p = ∈∩-intro {a} {xs} {ys ∩ zs} (∈∩-elimˡ (∈∩-elimˡ p)) (∈∩-intro {a} {ys} {zs} (∈∩-elimʳ xs (∈∩-elimˡ p)) (∈∩-elimʳ (xs ∩ ys) p))

  g : (a : X) → a ∈ (xs ∩ (ys ∩ zs)) → a ∈ ((xs ∩ ys) ∩ zs)
  g a p = ∈∩-intro {a} {xs ∩ ys} {zs} (∈∩-intro {a} {xs} {ys} (∈∩-elimˡ p) (∈∩-elimˡ (∈∩-elimʳ xs p))) (∈∩-elimʳ ys (∈∩-elimʳ xs p))

∩-comm : Commutative _≈L_ _∩_
∩-comm xs ys = extensionality _ _ λ a → f a xs ys , f a ys xs where
  f : (a : X) (xs ys : SortedList) → a ∈ (xs ∩ ys) → a ∈ (ys ∩ xs)
  f a xs ys p = ∈∩-intro {a} {ys} {xs} (∈∩-elimʳ xs p) (∈∩-elimˡ p)

∩-preserves-≈L : ∀ {x y u v} → x ≈L y → u ≈L v → (x ∩ u) ≈L (y ∩ v)
∩-preserves-≈L {xs} {ys} {us} {vs} p q = extensionality (xs ∩ us) (ys ∩ vs) λ x → f {x} p q , f {x} (≈L-sym p) (≈L-sym q) where
  f : ∀ {a xs us ys vs} → xs ≈L ys → us ≈L vs → a ∈ (xs ∩ us) → a ∈ (ys ∩ vs)
  f {a} {xs} {us} {ys} {vs} p q r = ∈∩-intro {a} {ys} {vs} (∈-preserves-≈L (∈∩-elimˡ r) p) (∈-preserves-≈L (∈∩-elimʳ xs r) q)

∩-annihilatesˡ : LeftZero _≈L_ [] _∩_
∩-annihilatesˡ _ = []

∩-annihilatesʳ : RightZero _≈L_ [] _∩_
∩-annihilatesʳ [] = []
∩-annihilatesʳ (cons x xs x#xs) = ∩-annihilatesʳ xs

∩-isSemigroup : IsSemigroup _≈L_ _∩_
IsMagma.isEquivalence (IsSemigroup.isMagma ∩-isSemigroup) = isEquivalence
IsMagma.∙-cong (IsSemigroup.isMagma ∩-isSemigroup) = ∩-preserves-≈L
IsSemigroup.assoc ∩-isSemigroup = ∩-assoc


----------------------------------------
-- Properties of _∩_ and _∪_ together --
----------------------------------------

∩-distrib-∪ˡ : _DistributesOverˡ_ _≈L_ _∩_ _∪_
∩-distrib-∪ˡ xs ys zs = extensionality _ _ λ x → f x , g x where
  f : (a : X) → a ∈ (xs ∩ (ys ∪ zs)) → a ∈ ((xs ∩ ys) ∪ (xs ∩ zs))
  f a p with ∈∪-elim {a} {ys} {zs} (∈∩-elimʳ xs p)
  ... | inj₁ a∈ys = ∈∪-introˡ {a} {xs ∩ ys} (∈∩-intro {a} {xs} {ys} (∈∩-elimˡ p) a∈ys) (xs ∩ zs)
  ... | inj₂ a∈zs = ∈∪-introʳ {a} {xs ∩ zs} (xs ∩ ys) (∈∩-intro {a} {xs} {zs} (∈∩-elimˡ p) a∈zs)

  g : (a : X) → a ∈ ((xs ∩ ys) ∪ (xs ∩ zs)) → a ∈ (xs ∩ (ys ∪ zs))
  g a p with ∈∪-elim {a} {xs ∩ ys} {xs ∩ zs} p
  ... | inj₁ q = ∈∩-intro {a} {xs} {ys ∪ zs} (∈∩-elimˡ q) (∈∪-introˡ (∈∩-elimʳ xs q) zs)
  ... | inj₂ q = ∈∩-intro {a} {xs} {ys ∪ zs} (∈∩-elimˡ q) (∈∪-introʳ ys (∈∩-elimʳ xs q))

∩-distrib-∪ʳ : _DistributesOverʳ_ _≈L_ _∩_ _∪_
∩-distrib-∪ʳ xs ys zs = extensionality _ _ λ x → f x , g x where
  f : (a : X) → a ∈ ((ys ∪ zs) ∩ xs) → a ∈ ((ys ∩ xs) ∪ (zs ∩ xs))
  f a p with ∈∪-elim {a} {ys} {zs} (∈∩-elimˡ {a} {ys ∪ zs} {xs} p)
  ... | inj₁ q = ∈∪-introˡ {a} {ys ∩ xs} (∈∩-intro {a} {ys} {xs} q (∈∩-elimʳ (ys ∪ zs) p)) (zs ∩ xs)
  ... | inj₂ q = ∈∪-introʳ {a} {zs ∩ xs} (ys ∩ xs) (∈∩-intro {a} {zs} {xs} q (∈∩-elimʳ (ys ∪ zs) p))

  g : (a : X) → a ∈ ((ys ∩ xs) ∪ (zs ∩ xs)) → a ∈ ((ys ∪ zs) ∩ xs)
  g a p with ∈∪-elim {a} {ys ∩ xs} {zs ∩ xs} p
  ... | inj₁ q = ∈∩-intro (∈∪-introˡ {a} {ys} (∈∩-elimˡ q) zs) (∈∩-elimʳ ys q)
  ... | inj₂ q = ∈∩-intro (∈∪-introʳ ys (∈∩-elimˡ q)) (∈∩-elimʳ zs q)

∪-distrib-∩ˡ : _DistributesOverˡ_ _≈L_ _∪_ _∩_
∪-distrib-∩ˡ xs ys zs = extensionality _ _ λ x → f x , g x where
  f : (a : X) → a ∈ (xs ∪ (ys ∩ zs)) → a ∈ ((xs ∪ ys) ∩ (xs ∪ zs))
  f a p with ∈∪-elim {a} {xs} {ys ∩ zs} p
  ... | inj₁ q = ∈∩-intro (∈∪-introˡ q ys) (∈∪-introˡ q zs)
  ... | inj₂ q = ∈∩-intro (∈∪-introʳ xs (∈∩-elimˡ q)) (∈∪-introʳ xs (∈∩-elimʳ ys q))

  g : (a : X) → a ∈ ((xs ∪ ys) ∩ (xs ∪ zs)) → a ∈ (xs ∪ (ys ∩ zs))
  g a p with ∈∪-elim {a} {xs} {ys} (∈∩-elimˡ p)
  ... | inj₁ a∈xs = ∈∪-introˡ a∈xs (ys ∩ zs)
  ... | inj₂ a∈ys with ∈∪-elim {a} {xs} {zs} (∈∩-elimʳ (xs ∪ ys) p)
  ... | inj₁ a∈xs = ∈∪-introˡ a∈xs (ys ∩ zs)
  ... | inj₂ a∈zs = ∈∪-introʳ xs (∈∩-intro a∈ys a∈zs)

∪-distrib-∩ʳ : _DistributesOverʳ_ _≈L_ _∪_ _∩_
∪-distrib-∩ʳ xs ys zs = extensionality _ _ λ x → f x , g x where
  f : (a : X) → a ∈ ((ys ∩ zs) ∪ xs) → a ∈ ((ys ∪ xs) ∩ (zs ∪ xs))
  f a p with ∈∪-elim {a} {ys ∩ zs} {xs} p
  ... | inj₁ q = ∈∩-intro (∈∪-introˡ {a} {ys} (∈∩-elimˡ q) xs) (∈∪-introˡ (∈∩-elimʳ ys q) xs)
  ... | inj₂ q = ∈∩-intro (∈∪-introʳ ys q) (∈∪-introʳ zs q)

  g : (a : X) → a ∈ ((ys ∪ xs) ∩ (zs ∪ xs)) → a ∈ ((ys ∩ zs) ∪ xs)
  g a p with ∈∪-elim {a} {ys} {xs} (∈∩-elimˡ p)
  ... | inj₂ a∈xs = ∈∪-introʳ (ys ∩ zs) a∈xs
  ... | inj₁ a∈ys with ∈∪-elim {a} {zs} {xs} (∈∩-elimʳ (ys ∪ xs) p)
  ... | inj₂ a∈xs = ∈∪-introʳ (ys ∩ zs) a∈xs
  ... | inj₁ a∈zs = ∈∪-introˡ (∈∩-intro a∈ys a∈zs) xs 

isPreSemiring : IsSemiringWithoutOne _≈L_ _∪_ _∩_ []
IsSemiringWithoutOne.+-isCommutativeMonoid isPreSemiring = isCommMonoid
IsSemiringWithoutOne.*-cong isPreSemiring = ∩-preserves-≈L
IsSemiringWithoutOne.*-assoc isPreSemiring = ∩-assoc
IsSemiringWithoutOne.distrib isPreSemiring = ∩-distrib-∪ˡ , ∩-distrib-∪ʳ
IsSemiringWithoutOne.zero isPreSemiring = ∩-annihilatesˡ , ∩-annihilatesʳ

-- TODO: Is also a commutative pre-semiring, and also + distributes over *

-------------------------------------------------
-- Properties of _∩_ with a Finite Carrier Set --
-------------------------------------------------

-- If there exists an element which is not in xs, then xs cannot be the unit of ∩.
∩-id-lemˡ : {x : X} {xs : SortedList} → x ∉ xs → ¬ (LeftIdentity _≈L_ xs _∩_)
∩-id-lemˡ {x} {xs} x∉xs id = x∉xs (∈∩-elimˡ (∈-preserves-≈L (∈insert-introˡ x xs) (≈L-sym (id (insert x xs)))))

∩-id-lemʳ : {x : X} {xs : SortedList} → x ∉ xs → ¬ (RightIdentity _≈L_ xs _∩_)
∩-id-lemʳ {x} {xs} x∉xs id = x∉xs (∈∩-elimʳ (insert x xs) $ ∈-preserves-≈L (∈insert-introˡ x xs) (≈L-sym (id (insert x xs))))


-- In this anonymous submodule we show that _∩_ has a unit iff the carrier set is finite (ie, enumerable).
module _ where
  private
    open import Data.List as L
    open import Data.List.Membership.Setoid as L using ()
    open import Data.List.Relation.Unary.Any as L using ()
    _∈'_ = L._∈_ (record { Carrier = X ; _≈_ = _≈_ ; isEquivalence = ≈-Eq })
    _∉'_ = L._∉_ (record { Carrier = X ; _≈_ = _≈_ ; isEquivalence = ≈-Eq })


  ∩-id-lemˡ' : {x : X} {xs : List X} → x ∉' xs → ¬ (LeftIdentity _≈L_ (insertion-sort xs) _∩_)
  ∩-id-lemˡ' {x} {xs} x∉xs id = ∩-id-lemˡ {x} {insertion-sort xs} (insertion-sort-preserves-∉ x∉xs) id

  ∩-id-lemʳ' : {x : X} {xs : List X} → x ∉' xs → ¬ (RightIdentity _≈L_ (insertion-sort xs) _∩_)
  ∩-id-lemʳ' {x} {xs} x∉xs id = ∩-id-lemʳ {x} {insertion-sort xs} (insertion-sort-preserves-∉ x∉xs) id

  -- Left Id → Enum
  ∩-idˡ→X-fin : (ε : List X) → LeftIdentity _≈L_ (insertion-sort ε) _∩_ → is-enumeration ε
  ∩-idˡ→X-fin xs id x with L.any? (x ≈?_) xs
  ... | yes p = p
  ... | no ¬p = ⊥-elim (∩-id-lemˡ' ¬p id)

  -- Right Id → Enum
  ∩-idʳ→X-fin : (ε : List X) → RightIdentity _≈L_(insertion-sort ε) _∩_ → is-enumeration ε
  ∩-idʳ→X-fin xs id x with L.any? (x ≈?_) xs
  ... | yes p = p
  ... | no ¬p = ⊥-elim (∩-id-lemʳ' ¬p id)

  -- Enum → Left Id
  X-fin→∩-idˡ : (ε : List X) → is-enumeration ε → LeftIdentity _≈L_ (insertion-sort ε) _∩_
  X-fin→∩-idˡ xs isEnum [] = ∩-annihilatesʳ (insertion-sort xs)
  X-fin→∩-idˡ xs isEnum (cons y ys p) =
    begin
      insertion-sort xs ∩ cons y ys p
    ≈⟨ ∩-preserves-≈L (extensionality (insertion-sort xs)
                                      (insert y (insertion-sort xs))
                                      (λ x → (λ _ → ∈insert-introʳ (insertion-sort-preserves-∈ (isEnum x)))
                                            , λ _ → insertion-sort-preserves-∈ (isEnum x))) (≡→≈L $ sym $ insert-consview p) ⟩
      ((cons y [] [] ∪ insertion-sort xs) ∩ (cons y [] [] ∪ ys))
    ≈⟨ (≈L-sym $ ∪-distrib-∩ˡ (cons y [] []) (insertion-sort xs) ys) ⟩
      (cons y [] []) ∪ (insertion-sort xs ∩ ys)
    ≈⟨⟩
      insert y (insertion-sort xs ∩ ys)
    ≈⟨ insert-preserves-≈L ≈-refl (X-fin→∩-idˡ xs isEnum ys) ⟩
      insert y ys
    ≈⟨ (≡→≈L $ insert-consview p) ⟩
      cons y ys p
    ∎ where open ≈L-Reasoning

  -- Enum → Right Id
  X-fin→∩-idʳ : (ε : List X) → is-enumeration ε → RightIdentity _≈L_ (insertion-sort ε) _∩_
  X-fin→∩-idʳ xs isEnum [] = ∩-annihilatesˡ (insertion-sort xs)
  X-fin→∩-idʳ xs isEnum (cons y ys p) with any? (y ≈?_) (insertion-sort xs)
  ... | yes q = ≈L-trans (insert-preserves-≈L ≈-refl (X-fin→∩-idʳ xs isEnum ys)) (≡→≈L $ insert-consview p)
  ... | no ¬q = ⊥-elim $ ¬q (insertion-sort-preserves-∈ {y} {xs} (isEnum y))


module WithFinCarrier (isEnum : Enumerated) where
  ∩-Unit : SortedList
  ∩-Unit = insertion-sort (proj₁ isEnum)

  ∩-idˡ : LeftIdentity _≈L_ ∩-Unit _∩_
  ∩-idˡ = X-fin→∩-idˡ (proj₁ isEnum) (proj₂ isEnum)

  ∩-idʳ : RightIdentity _≈L_ ∩-Unit _∩_
  ∩-idʳ = X-fin→∩-idʳ (proj₁ isEnum) (proj₂ isEnum)

  isSemiring : IsSemiring _≈L_ _∪_ _∩_ [] ∩-Unit
  IsSemiringWithoutAnnihilatingZero.+-isCommutativeMonoid (IsSemiring.isSemiringWithoutAnnihilatingZero isSemiring) = isCommMonoid
  IsSemiringWithoutAnnihilatingZero.*-cong (IsSemiring.isSemiringWithoutAnnihilatingZero isSemiring) = ∩-preserves-≈L
  IsSemiringWithoutAnnihilatingZero.*-assoc (IsSemiring.isSemiringWithoutAnnihilatingZero isSemiring) = ∩-assoc
  IsSemiringWithoutAnnihilatingZero.*-identity (IsSemiring.isSemiringWithoutAnnihilatingZero isSemiring) = ∩-idˡ , ∩-idʳ
  IsSemiringWithoutAnnihilatingZero.distrib (IsSemiring.isSemiringWithoutAnnihilatingZero isSemiring) = ∩-distrib-∪ˡ , ∩-distrib-∪ʳ
  IsSemiring.zero isSemiring = ∩-annihilatesˡ , ∩-annihilatesʳ

  isCommSemiring : IsCommutativeSemiring _≈L_ _∪_ _∩_ [] ∩-Unit
  IsCommutativeSemiring.isSemiring isCommSemiring = isSemiring
  IsCommutativeSemiring.*-comm isCommSemiring = ∩-comm

---------------------
-- Properties of ⊆ --
---------------------

⊆-respects-≈L : {xs xs' ys ys' : SortedList} → xs ≈L xs' → ys ≈L ys' → xs ⊆ ys → xs' ⊆ ys'
⊆-respects-≈L p q r s = ∈-preserves-≈L (r (∈-preserves-≈L s (≈L-sym p))) q

⊆-preserves-∈ : ∀ {xs ys} {a} → a ∈ xs → xs ⊆ ys → a ∈ ys
⊆-preserves-∈ p q = q p

insert-preserves-⊆ : ∀ {xs ys x y} → x ≈ y → xs ⊆ ys → insert x xs ⊆ insert y ys
insert-preserves-⊆ {xs} {ys} {x} {y} x≈y xs⊆ys {a} p with ∈∪-elim {a} {cons x [] []} {xs} p
... | inj₁ (here a≈x) = ∈∪-introˡ {a} {cons y [] []} (here $ ≈-trans a≈x x≈y) ys
... | inj₂ a∈xs = ∈∪-introʳ {a} {ys} (cons y [] []) (⊆-preserves-∈ a∈xs xs⊆ys)

insert⊆-intro : ∀ {x xs ys} → x ∈ ys → xs ⊆ ys → insert x xs ⊆ ys
insert⊆-intro x∈ys xs⊆ys a∈xxs with ∈insert-elim a∈xxs
... | inj₁ a≈x = ≈-preserves-∈ x∈ys (≈-sym a≈x)
... | inj₂ a∈xs = xs⊆ys a∈xs

⊆-[]-initial : ∀ {xs} -> [] ⊆ xs
⊆-[]-initial ()

⊆-weaken : ∀ {x xs ys} {fx : x # xs} → (cons x xs fx) ⊆ ys → xs ⊆ ys
⊆-weaken sub a∈xs = sub (there a∈xs)

⊆-step : ∀ {a xs ys} {p : a # xs} {q : a # ys} → xs ⊆ ys → cons a xs p ⊆ cons a ys q
⊆-step p (here x) = here x
⊆-step p (there q) = there (p q)

cons⊈[] : ∀ {x xs} {fx : x # xs} -> cons x xs fx ⊈ []
cons⊈[] {x} {xs} {fx} p with p (here ≈-refl)
... | ()

⊆-reflexive : {xs ys : SortedList} → xs ≈L ys → xs ⊆ ys
⊆-reflexive p q = ∈-preserves-≈L q p

⊆-refl : {xs : SortedList} → xs ⊆ xs
⊆-refl = ⊆-reflexive ≈L-refl

⊆-trans : Transitive _⊆_
⊆-trans p q = q ∘ p

⊆-antisym : Antisymmetric _≈L_ _⊆_
⊆-antisym p q = extensionality _ _ (λ x → p , q)

∪-upperboundˡ : (xs ys : SortedList) → xs ⊆ (xs ∪ ys)
∪-upperboundˡ xs ys p = ∈∪-introˡ p ys

∪-upperboundʳ : (xs ys : SortedList) → ys ⊆ (xs ∪ ys)
∪-upperboundʳ xs ys p = ∈∪-introʳ xs p

∪-lub : {xs ys zs : SortedList} → xs ⊆ zs → ys ⊆ zs → (xs ∪ ys) ⊆ zs
∪-lub {xs} {ys} p q r with ∈∪-elim {xs = xs} {ys} r
... | inj₁ s = p s
... | inj₂ s = q s

∪-supremum : Supremum _⊆_ _∪_
∪-supremum xs ys = ∪-upperboundˡ xs ys , ∪-upperboundʳ xs ys , λ _ → ∪-lub

∩-lowerboundˡ : (xs ys : SortedList) → (xs ∩ ys) ⊆ xs
∩-lowerboundˡ xs ys p = ∈∩-elimˡ p

∩-lowerboundʳ : (xs ys : SortedList) → (xs ∩ ys) ⊆ ys
∩-lowerboundʳ xs ys p = ∈∩-elimʳ xs p

∩-lub : {xs ys zs : SortedList} → zs ⊆ xs → zs ⊆ ys → zs ⊆ (xs ∩ ys)
∩-lub p q r = ∈∩-intro (p r) (q r)

-- ∩ is the infimum/meet/GLB of ⊆
∩-infimum : Infimum _⊆_ _∩_
∩-infimum xs ys = ∩-lowerboundˡ xs ys , ∩-lowerboundʳ xs ys , λ _ → ∩-lub

-- ⊆ is a partial order
⊆-isPO : IsPartialOrder _≈L_ _⊆_
IsPreorder.isEquivalence (IsPartialOrder.isPreorder ⊆-isPO) = isEquivalence
IsPreorder.reflexive (IsPartialOrder.isPreorder ⊆-isPO) = ⊆-reflexive
IsPreorder.trans (IsPartialOrder.isPreorder ⊆-isPO) = ⊆-trans
IsPartialOrder.antisym ⊆-isPO = ⊆-antisym

-- ⊆ is a lattice, with ∪ as the join and ∩ as the meet.
⊆-isLattice : IsLattice _≈L_ _⊆_ _∪_ _∩_
IsLattice.isPartialOrder ⊆-isLattice = ⊆-isPO
IsLattice.supremum ⊆-isLattice = ∪-supremum
IsLattice.infimum ⊆-isLattice = ∩-infimum

_⊆?_ : ∀ {x} xs ys → Dec (x ∈ xs → x ∈ ys)
_⊆?_ {x} xs ys with x ∈? xs
... | no x∉xs = yes λ x∈xs → ⊥-elim (x∉xs x∈xs)
... | yes x∈xs with x ∈? ys
... | yes x∈ys = yes λ _ → x∈ys
... | no x∉ys = no λ p → ⊥-elim (x∉ys (p x∈xs))

----------------------------------
-- Properties of set difference
----------------------------------
-[] : ∀ A → ([] -< A >) ≈L []
-[] [] = []
-[] (cons x xs x#xs) = -[] xs

-[]-subset : ∀ A x → (A -[ x ]) ⊆ A
-[]-subset (cons x xs x#xs) y p with x ≈? y
... | yes q = there p
... | no ¬q = ⊆-preserves-∈ p (⊆-step (-[]-subset xs y))

-<>-subset : ∀ A B → (A -< B >) ⊆ A
-<>-subset A [] p = p
-<>-subset [] (cons x xs x#xs) p = ∈-preserves-≈L p (-[] (cons x xs x#xs))
-<>-subset (cons y ys y#ys) (cons x xs x#xs) p with y ≈? x
... | yes q = there (-<>-subset ys xs p)
... | no ¬q = ⊆-preserves-∈ (-<>-subset (cons y (ys -[ x ]) (-[]-fresh ys x y y#ys)) xs p) (⊆-step (-[]-subset ys x))

-<>-subset' : ∀ A B C → A ⊆ B → (A -< C >) ⊆ B
-<>-subset' A B C sub p = sub (-<>-subset A C p)

--------------------------
-- Properties of filter --
--------------------------

filter-subset : ∀ xs P → filter P xs ⊆ xs
filter-subset (cons x xs x#xs) P y with P x
... | false =  ⊆-step {x} {p = filter-fresh x#xs} {q = x#xs} (filter-subset xs P) (there y)
... | true = ⊆-preserves-∈ y (⊆-step (filter-subset xs P))
