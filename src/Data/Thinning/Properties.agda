{-# OPTIONS --safe #-}

module Data.Thinning.Properties where

open import Data.Nat
open import Data.Nat.Properties using (+-suc)
open import Data.Empty
open import Data.Fin as F using ()
open import Data.Sum as S hiding (map)
open import Data.Sum.Properties as S
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Function as Fun

open import Data.Thinning.Base as Th

module _ where
  open Th.Fin

  -- Thinnings from 0 are propositions.
  thin0-prop : ∀ {i} → (θ1 θ2 : Thin 0 i) → θ1 ≡ θ2
  thin0-prop end end = refl
  thin0-prop (pad θ1) (pad θ2) = cong pad (thin0-prop θ1 θ2)

  -- The isomorphism with Fin.
  from-to : ∀ {i} (x : Thin 1 i) → x ≡ finIsoFrom (finIsoTo x)
  from-to (inj x) = cong inj (thin0-prop x zeros)
  from-to (pad x) = cong pad (from-to x)

  to-from : ∀ {i} (x : F.Fin i) → x ≡ finIsoTo (finIsoFrom x)
  to-from F.zero = refl
  to-from (F.suc x) = cong F.suc (to-from x)

-- Embedding the successor thinning yields suc.
embed-suc : ∀ {x} → F.suc ≗ (embed (inc x))
embed-suc F.zero = refl
embed-suc (F.suc y) = cong F.suc (embed-suc y)

embed-id : ∀ {i} (x : F.Fin i) → embed (Th.id i) x ≡ x
embed-id F.zero = refl
embed-id (F.suc x) = cong F.suc (embed-id x)

⊗-id : ∀ i {j} → (Th.id i ⊗ Th.id j) ≡ Th.id (i + j)
⊗-id ℕ.zero = refl
⊗-id (suc i) = cong inj (⊗-id i)

splitAt-embed-⊗ : ∀ {b b' n} (θ : Thin b b') (x : F.Fin (b + n))
                → S.map (embed θ) Fun.id (F.splitAt b x)
                ≡ F.splitAt b' (embed (θ ⊗ Th.id n) x)
splitAt-embed-⊗ end x = cong inj₂ (sym $ embed-id x)
splitAt-embed-⊗ (inj θ) F.zero = refl
splitAt-embed-⊗ {suc b} {suc b'} {n} (inj θ) (F.suc x) =
  begin
    map₁ (embed (inj θ)) (F.splitAt (suc b) (F.suc x))
  ≡⟨ S.map-map (F.splitAt b x) ⟩
    S.map₁ (F.suc ∘ embed θ) (F.splitAt b x)
  ≡⟨ S.map-map (F.splitAt b x) ⟨ -- looks like we just went back and forth, but the composite is able to compute a bit, while the chained maps cannot.
    map₁ F.suc (map₁ (embed θ) (F.splitAt b x))
  ≡⟨ cong (map₁ F.suc) (splitAt-embed-⊗ θ x) ⟩
    F.splitAt (suc b') (embed (inj θ ⊗ Th.id n) (F.suc x))
  ∎ where open ≡-Reasoning
splitAt-embed-⊗ {b} {suc b'} {n} (pad θ) x =
  begin
    map₁ (embed (pad θ)) (F.splitAt b x)
  ≡⟨ S.map-map (F.splitAt b x) ⟨
    map₁ F.suc (map₁ (embed θ) (F.splitAt b x))
  ≡⟨ cong (map₁ F.suc) (splitAt-embed-⊗ θ x) ⟩
    F.splitAt (suc b') (embed (pad θ ⊗ Th.id n) x)
  ∎ where open ≡-Reasoning

-- embed commutes with ↑ʳ
embed-↑ʳ : ∀ {i j k l} (θ1 : Thin i k) (θ2 : Thin j l) (x : F.Fin j)
         → (embed (θ1 ⊗ θ2) (i F.↑ʳ x)) ≡ k F.↑ʳ (embed θ2 x)
embed-↑ʳ end θ2 x = refl
embed-↑ʳ (inj θ1) θ2 x = cong F.suc (embed-↑ʳ θ1 θ2 x)
embed-↑ʳ (pad θ1) θ2 x = cong F.suc (embed-↑ʳ θ1 θ2 x)

sk+n≰n : ∀ {n} k → ¬ (Thin (suc k + n) n)
sk+n≰n zero (inj θ) = sk+n≰n 0 θ
sk+n≰n zero (pad θ) = sk+n≰n 1 θ
sk+n≰n (suc k) (inj θ) = sk+n≰n k (pad θ)
sk+n≰n (suc k) (pad {j = j} θ) = sk+n≰n {j} (2+ k) (subst (λ z → Thin (2+ z) j) (+-suc k j) θ)

1+n≰n : ∀ {n} → ¬ (Thin (suc n) n)
1+n≰n {n} = sk+n≰n {n} 0

id-unique : ∀ {i} → (θ1 θ2 : Thin i i) → θ1 ≡ θ2
id-unique end end = refl
id-unique (pad θ1) _ = ⊥-elim (1+n≰n θ1)
id-unique (inj θ1) (pad θ2) = ⊥-elim (1+n≰n θ2)
id-unique (inj θ1) (inj θ2) = cong inj (id-unique θ1 θ2)


-----------------------
-- Properties of Ext --
-----------------------

Ext→≡ : ∀ {i j k l n} {θ1 : Thin i j} {θ2 : Thin k l}
      → (eq1 : k ≡ i + n)
      → (eq2 : l ≡ j + n)
      → Ext θ1 θ2
      → θ1 ⊗ Th.id n ≡ subst₂ Thin eq1 eq2 θ2
Ext→≡ eq1 eq2 end = id-unique _ _
Ext→≡ refl refl (inj x) = cong inj (Ext→≡ refl refl x)
Ext→≡ refl refl (pad x) = cong pad (Ext→≡ refl refl x)

≡→Ext : ∀ {i j k l n} {θ1 : Thin i j} {θ2 : Thin k l}
      → (eq1 : k ≡ i + n)
      → (eq2 : l ≡ j + n)
      → θ1 ⊗ Th.id n ≡ subst₂ Thin eq1 eq2 θ2
      → Ext θ1 θ2
≡→Ext {θ1 = end} refl refl refl = end
≡→Ext {θ1 = inj θ} refl refl refl = inj (≡→Ext refl refl refl)
≡→Ext {θ1 = pad θ} refl refl refl = pad (≡→Ext refl refl refl)

id-Ext : ∀ {i n} → Ext (Th.id i) (Th.id (i + n))
id-Ext {zero} {n} = end
id-Ext {suc i} {n} = inj id-Ext

inc-Ext : ∀ {i j n}
        → j ≡ i + n
        → Ext (inc i) (inc j)
inc-Ext refl = pad id-Ext
