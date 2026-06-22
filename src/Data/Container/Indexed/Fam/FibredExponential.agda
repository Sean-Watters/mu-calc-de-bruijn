module Data.Container.Indexed.Fam.FibredExponential where

open import Data.Container.Indexed.Fam.Base
open import Data.Container.Indexed.Fam.Modality
open import Data.Container.Indexed.Fam.Combinator
open import Data.Container.Indexed.Fam.Morphism.Base
open _⇒_
open import Data.Maybe
open import Data.Product hiding (curry; uncurry)
open import Data.Sum
open import Data.Sum.MoreProps
open import Function
open import Relation.Binary.PropositionalEquality hiding (J)

private variable
  I J : Set

_⟨⇒⟩_ : (C D : Container I J) → (∀ (i : I) → Container I J)
(C ⟨⇒⟩ D) i .Shape j = {!C .Shape!}
(C ⟨⇒⟩ D) i .Position = {!!}
