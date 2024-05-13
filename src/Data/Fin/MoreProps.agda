{-# OPTIONS --with-K #-}
module Data.Fin.MoreProps where

open import Data.Nat hiding (_>_) renaming (_<_ to _<ℕ_)
open import Data.Fin
open import Data.Fin.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.WithK
open import Algebra.Structures.Propositional
open import Function

<-isPropStrictTotalOrder : ∀ n → IsPropStrictTotalOrder (_≡_ {A = Fin n}) _<_
IsPropStrictTotalOrder.isSTO (<-isPropStrictTotalOrder n) = <-isStrictTotalOrder
IsPropStrictTotalOrder.≈-prop (<-isPropStrictTotalOrder n) = ≡-irrelevant
IsPropStrictTotalOrder.<-prop (<-isPropStrictTotalOrder n) = ≤-irrelevant

>-isPropStrictTotalOrder : ∀ n →  IsPropStrictTotalOrder (_≡_ {A = Fin n}) _>_
>-isPropStrictTotalOrder n = IsPropStrictTotalOrder.flip-PSTO (<-isPropStrictTotalOrder n)

toℕ-inject₁-fromℕ< : ∀ {x y n : ℕ} → (px : x <ℕ n) (py : y <ℕ n) → x <ℕ y → toℕ (inject₁ (fromℕ< px)) <ℕ toℕ (inject₁ (fromℕ< py))
toℕ-inject₁-fromℕ< (s≤s z≤n) (s≤s (s≤s py)) _ = s≤s z≤n
toℕ-inject₁-fromℕ< (s≤s (s≤s px)) (s≤s (s≤s py)) (s≤s q) = s≤s (toℕ-inject₁-fromℕ< (s≤s px) (s≤s py) q)

inject₁-fromℕ< : ∀ {x y n : ℕ} → (px : x <ℕ n) (py : y <ℕ n) → x <ℕ y → inject₁ (fromℕ< px) < inject₁ (fromℕ< py)
inject₁-fromℕ< x<n y<n x<y =  toℕ-cancel-< (toℕ-inject₁-fromℕ< x<n y<n x<y)

fromℕ<-cancel-< : ∀ {x y n} → (x<n : x <ℕ n) (y<n : y <ℕ n) → x <ℕ y → fromℕ< x<n < fromℕ< y<n
fromℕ<-cancel-< (s≤s z≤n) (s≤s (s≤s y<n)) x = s≤s z≤n
fromℕ<-cancel-< (s≤s (s≤s x<n)) (s≤s (s≤s y<n)) (s≤s q) = s≤s (fromℕ<-cancel-< (s≤s x<n) (s≤s y<n) q)
