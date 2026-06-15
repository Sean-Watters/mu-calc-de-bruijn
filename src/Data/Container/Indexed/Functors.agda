{-# OPTIONS --safe #-}
module Data.Container.Indexed.Functors where

open import Function
open import Relation.Binary.PropositionalEquality hiding (J) 

-- Getting a handle on the indexed categories at play
-- Basically copying the Indexed Containers JFP paper

private variable
  I J K L : Set

------------------------------------------------------
-- The category Fam I of I-indexed families of sets.
------------------------------------------------------

-- Indexed families of sets.
Fam : Set → Set₁
Fam X = X → Set

-- Morphisms of indexed families are indexed families of functions.
_→*_ : Fam I → Fam I → Set
A →* B = ∀ i → A i → B i

-- The identity morphism of families;
-- at every index i, it is the identity function.
id* : {A : Fam I} → A →* A
id* _ = id

-- Composition
_∘*_ : {A B C : Fam I}
     → (B →* C) → (A →* B) → (A →* C)
(f ∘* g) i = f i ∘ g i

-------------------------------------------
-- Singly Indexed Functors `Fam I → Set`
-------------------------------------------

-- Actions on objects look like this:
IFunc : Set → Set₁
IFunc I = Fam I → Set
-- that is, `(I → Set) → Set`

-- Actions on morpshism look like this:
IFunc-map : {I : Set} → (F : IFunc I) → Set₁
IFunc-map F = ∀ {A B} → (A →* B) → (F A → F B)

-- Singly indexed functors from Fam I to Set, without laws
record RawIFunc (I : Set) : Set₁ where
  field
    obj : IFunc I
    mor : IFunc-map obj


record LawfulIFunc (I : Set) : Set₁ where
  field
    raw : RawIFunc I
  open RawIFunc raw
  field
    preserves-id : ∀ {A} → mor {A} id* ≗ id
    preserves-∘ : ∀ {A B C}
                → (g : B →* C) (f : A →* B)
                → mor (g ∘* f) ≗ (mor g) ∘ (mor f)

-- Not-necessarily-natural transformations
_⇒_ : (F G : IFunc I) → Set₁
F ⇒ G = ∀ A → F A → G A


-------------------------------------------
-- Doubly Indexed Functors `Fam I → Fam J`
-------------------------------------------

-- This is equivalent to `J → IFunc I`
IFunc* : (I J : Set) → Set₁
IFunc* I J = Fam I → Fam J

IFunc*-map : (F : IFunc* I J) → Set₁
IFunc*-map F = ∀ {A B} → (A →* B) → (F A →* F B)

record RawIFunc* (I J : Set) : Set₁ where
  field
    obj : IFunc* I J
    mor : IFunc*-map obj

record LawfulIFunc* (I J : Set) : Set₁ where
  field
    raw : RawIFunc* I J
  open RawIFunc* raw
  field
    -- preserves-id : ∀ {A : Fam I} (i : I) (j : J) → mor (id* {A = A}) ≗ id* 
    -- preserves-∘ : ∀ {A B C}
    --             → (g : B →* C) (f : A →* B)
    --             → mor (g ∘* f) ≗ ((mor g) ∘* (mor f))

-- Natural transformations of doubly indexed functors
_⇒*_ : (F G : IFunc* I J) → Set₁
F ⇒* G = ∀ A → F A →* G A

-- Reindexing the I
Δₗ : (I → K) → IFunc* I J → IFunc* K J
Δₗ f F X = F (X ∘ f)

-- Reindexing the J
Δᵣ : (L → J) → IFunc* I J → IFunc* I L
Δᵣ f F X = (F X) ∘ f

-- Reindexing by both
Δ₂ : (I → K) → (L → J) → IFunc* I J → IFunc* K L
Δ₂ f g F X =  (F (X ∘ f)) ∘ g

-- Σ and Π are left and right adjoint to Δ
-- TODO

