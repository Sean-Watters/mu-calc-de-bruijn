module Axiom.UniquenessOfIdentityProofs.Properties where

open import Axiom.UniquenessOfIdentityProofs
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Sum.Properties
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Isomorphism
open import Relation.Nullary

UIP-⊤ : UIP ⊤
UIP-⊤ {tt} {tt} refl refl = refl

whisker : ∀ {ℓ} {A B : Set ℓ} (f : A -> B)  (g : B -> A)
        → (α : ∀ x → f (g x) ≡ x) {x y : B} (p : x ≡ y)
        → p ≡  trans (sym (α x)) (trans (cong f (cong g p)) (α y))
whisker f g α {x = x} refl = sym (trans-symˡ (α x))

UIP-Retract : ∀ {ℓ} {A B : Set ℓ} (f : A -> B)  (g : B -> A)
            → (∀ x → f (g x) ≡  x) -> UIP A -> UIP B
UIP-Retract f g α setA {x = x} {y} p q =
  begin
    p
  ≡⟨ whisker f g α p ⟩
    trans (sym (α x)) (trans (cong f (cong g p)) (α y))
  ≡⟨ cong (λ z → trans (sym (α x)) (trans (cong f z) (α y))) (setA (cong g p) (cong g q)) ⟩
    trans (sym (α x)) (trans (cong f (cong g q)) (α y))
  ≡⟨ sym (whisker f g α q) ⟩
    q
  ∎ where open ≡-Reasoning

-- Propositions have contractible identities
prop-contr-≡ : ∀ {ℓ} {X : Set ℓ} → Irrelevant X
             → {x y : X} → Σ[ c ∈ x ≡ y ] ((p : x ≡ y) → c ≡ p)
prop-contr-≡ {ℓ} {X} propX {x} {y} =
  (propX x y) ,
  λ { refl → trans (canon (sym (propX y y))) (trans-symˡ (propX x x)) }
  where
    canon : {x y : X} → (p : x ≡ y) → propX x y ≡ trans p (propX y y)
    canon refl = refl

-- Propositions have UIP
UIP-prop : ∀ {ℓ} {X : Set ℓ} → Irrelevant X → UIP X
UIP-prop propX {x} {y} p q = trans (sym (proj₂ (prop-contr-≡ propX) p))
                                   (proj₂ (prop-contr-≡ propX) q)

-- In particular, if some type X has UIP, then so does its identity type
-- (and so on, all the way up)
UIP-≡ : ∀ {ℓ} {X : Set ℓ} → UIP X → (x y : X) → UIP (x ≡ y)
UIP-≡ uipX x y = UIP-prop uipX



-- UIP is closed under coproducts

inj₁-lem : ∀ {ℓx ℓy} {X : Set ℓx} {Y : Set ℓy} {x y : X} (p : _≡_ {A = X ⊎ Y} (inj₁ x) (inj₁ y)) → p ≡ cong inj₁ (inj₁-injective p)
inj₁-lem refl = refl

inj₁-injective-injective : ∀ {ℓx ℓy} {X : Set ℓx} {Y : Set ℓy} {x y : X} (p q : _≡_ {A = X ⊎ Y} (inj₁ x) (inj₁ y)) → inj₁-injective p ≡ inj₁-injective q → p ≡ q
inj₁-injective-injective p q u = trans (inj₁-lem p) (trans (cong (cong inj₁) u) (sym $ inj₁-lem q))

inj₂-lem : ∀ {ℓx ℓy} {X : Set ℓx} {Y : Set ℓy} {x y : Y} (p : _≡_ {A = X ⊎ Y} (inj₂ x) (inj₂ y)) → p ≡ cong inj₂ (inj₂-injective p)
inj₂-lem refl = refl

inj₂-injective-injective : ∀ {ℓx ℓy} {X : Set ℓx} {Y : Set ℓy} {x y : Y} (p q : _≡_ {A = X ⊎ Y} (inj₂ x) (inj₂ y)) → inj₂-injective p ≡ inj₂-injective q → p ≡ q
inj₂-injective-injective p q u = trans (inj₂-lem p) (trans (cong (cong inj₂) u) (sym $ inj₂-lem q))

UIP-⊎ : ∀ {ℓx ℓy} {X : Set ℓx} {Y : Set ℓy} → UIP X → UIP Y → UIP (X ⊎ Y)
UIP-⊎ uipX uipY {inj₁ x} {inj₁ y} p q = inj₁-injective-injective p q $ uipX (inj₁-injective p) (inj₁-injective q)
UIP-⊎ uipX uipY {inj₂ x} {inj₂ y} p q = inj₂-injective-injective p q $ uipY (inj₂-injective p) (inj₂-injective q)


-- UIP is closed under non-dependent pairs

plumb : ∀ {ℓa ℓb ℓc ℓd} {A : Set ℓa} {B : Set ℓb} {C : A → A → Set ℓc} {D : B → B → Set ℓd}
      → (f : (x y : A) → C x y) (g : (x y : B) → D x y)
      → (p q : A × B) → C (proj₁ p) (proj₁ q) × D (proj₂ p) (proj₂ q)
plumb f g (a1 , b1) (a2 , b2) = f a1 a2 , g b1 b2

,-lem : ∀ {ℓx ℓy} {X : Set ℓx} {Y : Set ℓy} {x1 x2 : X} {y1 y2 : Y} (p : (x1 , y1) ≡ (x2 , y2))
          → p ≡ cong₂ _,_ (proj₁ $ ,-injective p) (proj₂ $ ,-injective p)
,-lem refl = refl

repackage : ∀ {ℓx ℓy} {X : Set ℓx} {Y : Set ℓy} {x1 x2 : X} {y1 y2 : Y}
          → (p q : (x1 , y1) ≡ (x2 , y2))
          → proj₁ (,-injective p) ≡ proj₁ (,-injective q) × proj₂ (,-injective p) ≡ proj₂ (,-injective q)
          → p ≡ q
repackage p q (u , v) = trans (,-lem p) (trans (cong₂ (cong₂ _,_) u v) (sym $ ,-lem q))

UIP-× : ∀ {ℓx ℓy} {X : Set ℓx} {Y : Set ℓy} → UIP X → UIP Y → UIP (X × Y)
UIP-× uipX uipY {x1 , y1} {x2 , y2} p q = repackage p q $ plumb uipX uipY (,-injective p) (,-injective q)

-- The full, general case:
-- If both args of a sigma type are always sets, then the sigma type is a set.
-- ie, UIP is closed under dependent pairs.

cong-, : ∀ {ℓx ℓy} {X : Set ℓx} {Y : X → Set ℓy} {x1 x2 : X} {y1 : Y x1} {y2 : Y x2}
       → (p : x1 ≡ x2)
       → subst Y p y1 ≡ y2
       → (x1 , y1) ≡ (x2 , y2)
cong-, refl refl = refl


cong₂-cong-, : ∀ {ℓx ℓy} {X : Set ℓx} {Y : X → Set ℓy} {x1 x2 : X} {y1 : Y x1} {y2 : Y x2}
             → {p q : x1 ≡ x2} {p' : subst Y p y1 ≡ y2} {q' : subst Y q y1 ≡ y2}
             → (eqL : p ≡ q)
             → subst (λ z → subst Y z y1 ≡ y2) eqL p' ≡ q'
             → cong-, p p' ≡ cong-, q q'
cong₂-cong-, refl refl = refl


,-lem' : ∀ {ℓx ℓy} {X : Set ℓx} {Y : X → Set ℓy} {x1 x2 : X} {y1 : Y x1} {y2 : Y x2}
       → (uipX : UIP X) (uipY : ∀ x → UIP (Y x))
       → (p : (x1 , y1) ≡ (x2 , y2))
       → p ≡ cong-, (,-injectiveˡ p) (,-injectiveʳ-≡ uipX p (,-injectiveˡ p))
,-lem' {Y = Y} {x1 = x1} {y1 = y1} uipX uipY refl rewrite UIP-≡ uipX x1 x1 (uipX refl refl) refl = refl

repackage' : ∀ {ℓx ℓy} {X : Set ℓx} {Y : X → Set ℓy} {x1 x2 : X} {y1 : Y x1} {y2 : Y x2}
           → (uipX : UIP X) (uipY : ∀ x → UIP (Y x))
           → (p q : (x1 , y1) ≡ (x2 , y2))
           → (u : ,-injectiveˡ p ≡ ,-injectiveˡ q)
           → subst (λ z → subst Y z y1 ≡ y2) u (,-injectiveʳ-≡ uipX p (,-injectiveˡ p)) ≡ ,-injectiveʳ-≡ uipX q (,-injectiveˡ q)
           → p ≡ q
repackage' uipX uipY p q u v = trans (,-lem' uipX uipY p) (trans (cong₂-cong-, u v) (sym $ ,-lem' uipX uipY q))

UIP-Σ :  ∀ {ℓx ℓy} {X : Set ℓx} {Y : X → Set ℓy} → UIP X
       → (∀ x → UIP (Y x)) → UIP (Σ[ x ∈ X ] Y x)
UIP-Σ {Y = Y} uipX uipY {x1 , y1} {x2 , y2} p q
  = repackage' uipX uipY p q
               (uipX (,-injectiveˡ p) (,-injectiveˡ q))
               (uipY x2 (subst (λ z → subst (λ v → Y v) z y1 ≡ y2)
                        (uipX (,-injectiveˡ p) (,-injectiveˡ q)) (,-injectiveʳ-≡ uipX p (,-injectiveˡ p))) (,-injectiveʳ-≡ uipX q (,-injectiveˡ q)))

-- Lemma: UIP is preserved by isomorphism.
UIP-≃ : ∀ {ℓ} {X : Set ℓ} {Y : Set ℓ} → UIP X → X ≃ Y → UIP Y
UIP-≃ uipX iso = UIP-Retract (to iso) (from iso) (λ y → sym (to-from iso y)) uipX
  where open _≃_
