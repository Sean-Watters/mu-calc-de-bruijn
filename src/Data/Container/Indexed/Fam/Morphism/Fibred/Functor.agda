
module Data.Container.Indexed.Fam.Morphism.Fibred.Functor where

open import Data.Container.Indexed.Fam.Base
open import Data.Container.Indexed.Fam.Morphism.Fibred
open import Data.Container.Indexed.Fam.Morphism.Base

private variable
  I J : Set
  C D : Container I J

to : C ⇒ D → (∀ j → IHom C D j)
to f j .IHom.fw = f .fw {j}
to f j .IHom.bw = f .bw {j}

from : (∀ j → IHom C D j) → C ⇒ D
from f .fw = f _ .IHom.fw
from f .bw = f _ .IHom.bw
