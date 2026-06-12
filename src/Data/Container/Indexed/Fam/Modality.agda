
module Data.Container.Indexed.Fam.Modality where

open import Data.Container.Indexed.Fam.Base
open import Data.Product

record ◇ {I J : Set} (C : Container I J) {X : I → Set}
         (P : ∀ {i} → X i → Set)
         {j : J} (cx : ⟦ C ⟧ X j) : Set
         where
         
       constructor any
       -- field proof : Σ[ i ∈ I ]
                     -- Σ[ p ∈ C .Position (cx .proj₁) i ]
                     -- P (proj₂ cx p)
       -- 
       -- todo: should I be suspicious that this has to work for all i?
       field proof : ∀ (i : I) → 
                     Σ[ p ∈ C .Position (cx .proj₁) i ]
                     P (proj₂ cx p)
