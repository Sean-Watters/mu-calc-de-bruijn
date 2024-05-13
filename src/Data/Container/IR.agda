-- From (Ghani & Hancock, 2011).
module Data.Container.IR where

open import Level
open import Data.Container renaming (Container to Cont'; ⟦_⟧ to ⟦_⟧C; map to map-Cont)
open import Data.Unit
open import Data.Product
open import Function

private
  Container = Cont' 0ℓ 0ℓ

-- Families
Fam : Set₁ → Set₁
Fam D = Σ[ U ∈ Set ] (U → D)

-- Large families
LFam : Set₁ → Set₁ → Set₁
LFam I O = Σ[ A ∈ Set ] ((A → I) → O)

-- Squashing Fam and LFam together
LCFam : Set₁ → Set₁ → Set₁
LCFam I O = Σ[ H ∈ Container ] (⟦ H ⟧C I → O)

map-LCFam : {I D D' : Set₁} → (D → D') → (LCFam I D → LCFam I D')
map-LCFam g (A , F) = A , g ∘ F

-- Dybjer-Setzer IR codes
data IR (I O : Set₁) : Set₁ where
  ι : O → IR I O
  σδ : LCFam I (IR I O) → IR I O

-- fold : {I O X : Set₁} → (O → X) → (LCFam I X → X) → IR I O → X
-- fold i k (ι o) = i o
-- fold i k (σδ F) = k (map-LCFam (fold i k) F)


-- -- Decoding of IR codes to operators on families.
-- ⟦_⟧₀ : ∀ {D} → IR D → Fam D → Set
-- ⟦ ι d ⟧₀ X = ⊤
-- ⟦ σ A f ⟧₀ X = Σ[ a ∈ A ] (⟦ f a ⟧₀ X)
-- ⟦ δ A F ⟧₀ (U , T) = Σ[ g ∈ (A → U) ] (⟦ F (T ∘ g) ⟧₀ (U , T))

-- ⟦_⟧₁ : ∀ {D} → (c : IR D) → (X : Fam D) → (⟦ c ⟧₀ X → D)
-- ⟦ ι d ⟧₁ X _ = d
-- ⟦ σ A f ⟧₁ X (a , i) = ⟦ f a ⟧₁ X i
-- ⟦ δ A F ⟧₁ (U , T) (g , i) = ⟦ F (T ∘ g) ⟧₁ (U , T) i
