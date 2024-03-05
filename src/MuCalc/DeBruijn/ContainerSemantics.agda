
open import Algebra.Structures.Propositional
open import Relation.Unary.Countable
open import Relation.Binary.PropositionalEquality

module MuCalc.DeBruijn.ContainerSemantics
  {At : Set}
  {_<A_ : At → At → Set}
  (<A-STO : IsPropStrictTotalOrder _≡_ _<A_)
  (At-countable : IsCountable At)
  -- The model
  (S : Set) -- A set of states
  (R : S → S → Set) -- A transition relation on S
  (V : At → S → Set) -- A valuation function for propositions at states
  where

open import Level renaming (zero to fzero; suc to fsuc)
open import Data.Fin hiding (_-_) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using ()
open import Data.Fin.MoreProps renaming (<-isPropStrictTotalOrder to Fin-STO)
open import Data.Vec hiding (toList; filter; insert)
open import Data.Nat
open import Data.Nat.Properties using ()
open import Data.Nat.MoreProps renaming (<-isPropStrictTotalOrder to ℕ-STO)
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Container.Indexed renaming (Container to Container'; ⟦_⟧ to `⟦_⟧` ; μ to `μ`)
open import Data.Container.Indexed.Combinator using (const) renaming (_×_ to _`×`_; _⊎_ to _`+`_; Π to All; Σ to Any)
open import Data.W.Indexed
open import Relation.Nullary
open import Relation.Binary
open import Function using (_∘_)

open import MuCalc.DeBruijn.Base <A-STO At-countable renaming (⊤ to ⊤'; ⊥ to ⊥')

private
  -- we always want small things, so define an alias where the levels are
  -- fixed at 0
  Container : Set → Set → Set₁
  Container I O = Container' I O 0ℓ 0ℓ

------------------------------------------------------------------------------

-- mkUnary : ∀ {n} → Container (S × Fin n) S 0ℓ 0ℓ → Container S S  0ℓ 0ℓ
-- mkUnary {m} (C ◃ R / n) = C ◃ (λ c → R c × Fin m) / {!!}

-- interpretVec' : ∀ {n} → Vec (S → Set) n → (S → Vec Set n)
-- interpretVec' [] s = []
-- interpretVec' (x ∷ xs) s = (x s) ∷ (interpretVec' xs s)

interpretVec : ∀ {n} → Vec (S → Set) n → (S × Fin n → Set)
interpretVec xs (s , m) = lookup xs m s


-- might hope these types could be generalised?
-- on the other hand, maybe not posible to generalise, as □ and ◇ look that way too


projR-with-default : {A B : Set} → B → A ⊎ B → B
projR-with-default d (inj₁ a) = d
projR-with-default d (inj₂ b) = b

ignore-input : ∀ {I O} → Container (I ⊎ O) O → Container O O
ignore-input (C ◃ R / n) = C ◃ R / (λ {o} c Rc → projR-with-default o (n c Rc))

par-ap : ∀ {I O} → Container (I ⊎ O) (I ⊎ O) → Container I O → Container O O
par-ap (C1 ◃ R1 / n1) (C2 ◃ R2 / n2) = {! !} ◃ {!!} / {!!}

data C-Mu {I O} (C : Container (I ⊎ O) O) : O → Set where
  inn : {o : O} → `μ` {0ℓ} {0ℓ} {0ℓ} {O} (ignore-input C) o → C-Mu C o

Mu' : ∀ {I O} → Container (I ⊎ O) O → Container I O
Mu' {I} {O} c = C-Mu c ◃ (λ { (inn (sup (C , R))) → {!next c c' r'!}}) / {!!} where
  Mu-R : {o : O} → (C : Command (ignore-input c) o)
       → ((r : Response (ignore-input c) C) → W (ignore-input c) (next (ignore-input c) C r))
       → Response (ignore-input c) C
  Mu-R = {!!}

map' : ∀ {I I' O} → (I → I') → Container I O → Container I' O
map' f (C ◃ R / n) = C ◃ R / λ c x → f (n c x)

dist-fin : ∀ {n} → S × Fin (suc n) → S × Fin n ⊎ S
dist-fin {n} (s , Fin.zero) = inj₂ s
dist-fin {n} (s , Fin.suc m) = inj₁ (s , m)

Mu : ∀ {n} → Container (S × Fin (suc n)) S → Container (S × Fin n) S
Mu {n} C = Mu' {S × Fin n} {S} (map' dist-fin C)

Nu : ∀ {n} → Container (S × Fin (suc n)) S → Container (S × Fin n) S
Nu = {!!}

mkCont : {n : ℕ} → μML n → Container (S × Fin n) S
mkCont {n} (var x) = (λ s → ⊤) ◃ (λ _ → ⊤) / λ {s} _ _ → s , x
mkCont (μML₀ ⊤') = const (λ _ → ⊤)
mkCont (μML₀ ⊥') = const(λ _ → ⊥)
mkCont (μML₀ (at x)) = const (V x)
mkCont (μML₀ (¬at x)) = const (λ s → ¬ (V x s))
-- This looks so close to being a general case of Π, but I think not quite
mkCont (μML₁ □ ϕ) = (λ s → (x : S) → R s x → Command (mkCont ϕ) x)
                  ◃ (λ {s} c → Σ[ x ∈ S ] Σ[ Rsx ∈ R s x ] Response (mkCont ϕ) (c x Rsx))
                  / λ { c (x , Rsx , r) → next (mkCont ϕ) (c x Rsx) r }
mkCont (μML₁ ◆ ϕ) = (λ s → Σ[ x ∈ S ] Σ[ Rsx ∈ R s x ] Command (mkCont ϕ) x )
                  ◃ (λ { (x , Rsx , c) → Response (mkCont ϕ) c})
                  / (λ { (x , Rsx , c) r → next (mkCont ϕ) c r })
mkCont (μML₂ ∧ ϕ ψ) = mkCont ϕ `×` mkCont ψ
mkCont (μML₂ ∨ ϕ ψ) = mkCont ϕ `+` mkCont ψ
mkCont (μMLη μ ϕ) = Mu (mkCont ϕ)
mkCont (μMLη ν ϕ) = Nu (mkCont ϕ)

⟦_⟧ : ∀ {n} → μML n → Vec (S → Set) n → S → Set
⟦_⟧ {n} ϕ i = `⟦_⟧` (mkCont ϕ) (interpretVec i)




{-

⟦ var x ⟧ i s = lookup i x s
⟦ μML₀ ⊤' ⟧ _ _ = ⊤
⟦ μML₀ ⊥' ⟧ _ _ = ⊥
⟦ μML₀ (at p) ⟧ _ s = V p s
⟦ μML₀ (¬at p) ⟧ _ s = ¬ (V p s)
⟦ μML₁ □ ϕ ⟧ i s = (y : S) → R s y → ⟦ ϕ ⟧ i y
⟦ μML₁ ◆ ϕ ⟧ i s = Σ[ y ∈ S ] (R s y) × ⟦ ϕ ⟧ i y
⟦ μML₂ ∧ ϕ ψ ⟧ i s = (⟦ ϕ ⟧ i s) × (⟦ ψ ⟧ i s)
⟦ μML₂ ∨ ϕ ψ ⟧ i s = (⟦ ϕ ⟧ i s) ⊎ (⟦ ψ ⟧ i s)
⟦_⟧ {n} (μMLη μ ϕ) i s = Mu ({!μML n!} ◃ {!!} / {!!}) s -- Mu ϕ i s
  -- --λ (X : S → Set) → ⟦ ϕ ⟧ (X ∷ i)
⟦ μMLη ν ϕ ⟧ i s = {!!}

-}
