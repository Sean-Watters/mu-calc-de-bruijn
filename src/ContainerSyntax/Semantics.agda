module ContainerSyntax.Semantics where

open import Level using () renaming (zero to 0ℓ)
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Fin
open import Data.Vec as Vec
open import Data.Product
open import Data.Sum as Sum
open import Data.Container.Indexed.Fam renaming (⟦_⟧ to ⟦_⟧c)
open import Function
open import Relation.Binary.PropositionalEquality hiding (J)

open import ContainerSyntax.Base

-- Working only with inductive types for now.
-- Can add coinduction once this is all working.

AsCont : ∀ {n} → Ty n → Container (Fin n) ⊤
AsCont `0` = ⟨⊥⟩
AsCont `1` = ⟨⊤⟩
AsCont (l `+` r) = AsCont l ⟨+⟩ AsCont r
AsCont (l `×` r) = AsCont l ⟨×⟩ AsCont r
AsCont (`Σ` X f) = ⟨Σ⟩ (const X) (λ x → AsCont (f x))
AsCont (`μ` ty) = ⟨μ⟩ (⟨mapI⟩ Sum.[ suc , const Fin.zero ] (AsCont ty))
AsCont {n} (`var` x) = (const ⊤) ▷ (λ _ y → x ≡ y)

-- Still just working with the inductive fragment.
-- We want to think of the meaning of one of these type terms as a functor `(Set^n) → Set`,
-- where n is the number of free variables, s.t. the `Set^n` represents the meanings of those vars.
-- The extension of a container is some functor `Set → Set`.
-- So if we use simple containers, we have to take our `Γ : Set^n` and glue it together
-- as `Σ[ y ∈ Fin n ] (lookup Γ y)`.

-- But that approach has a problem --- we want `⟦ var x ⟧ Γ ≅ lookup Γ x`, but there is no way to enforce
-- the connection between the x's without indexed containers.
-- In non-indexed containers, the var case would just be indentity.
-- Then we'd have `⟦ var x ⟧ Γ ≅ Σ[ y ∈ Var ] (lookup Γ y)
-- So x could potentially be associated with the meaning of any arbitrary y, rather than the meaning of
-- x in particular.

-- So, we need to use indexed containers. To minimise on noise (eg the need to map (Fin n → Fin n ⊎ ⊤) in
-- the μ case) and margin of error, we could use singly indexed containers (we only need position indices,
-- not shape), but for now let's just use what we have in the library. All it means that there will be extra
-- ⊤'s floating around that we need to ignore.

-- Now we no longer have to glue up the vector of sets; `lookup Γ` is a family `Fin n → Set`, just as Grothendieck intended.
⟦_⟧' : ∀ {n} → Ty n → Vec Set n → Set
⟦ ty ⟧' Γ = ⟦ AsCont ty ⟧c (lookup Γ) tt


-- And now by mapping ⟦_⟧' over the context, we get the the meaning of a type in a context of type terms, rather than of sets.

interpret-context : ∀ {n} → Context n → Vec Set n
interpret-context [] = []
interpret-context (Γ -, ty)
  = let ss = interpret-context Γ
    in ⟦ ty ⟧' ss ∷ ss

-- So we get agda sets for our types
⟦_⟧ : ∀ {n} → Ty n → Context n → Set
⟦ ty ⟧ Γ = ⟦ ty ⟧' (interpret-context Γ)

-- If the term is closed, the context is free.
⟦_⟧ε : `Set` → Set
⟦ ty ⟧ε = ⟦ ty ⟧ []
