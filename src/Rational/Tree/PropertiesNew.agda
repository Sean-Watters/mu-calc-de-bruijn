{-# OPTIONS --safe --guardedness --with-K #-}
module Rational.Tree.PropertiesNew where

open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Fin as F using (Fin; zero; suc)
open import Data.Fin.Renaming
open import Data.Nat
open import Data.Empty
open import Data.Thinning as Th hiding (id)
open import MuCalc.Base using (Op₁; Op₂; Opη)
open import Codata.NWFTree as NWF using (∞NWFTree; NWFTree; _~_; here; there)
open import Rational.TreeNew as R
open import Relation.Nullary

------------------------------------
-- Functions that preserve NonVar --
------------------------------------

-- rename-NonVar - defined in Rational.Tree, beacuse it's needed to implement ++


lookup-NonVar : ∀ {X n} → (Γ : Scope X n) → (x : Fin n) → NonVar (lookup Γ x)
lookup-NonVar (_,-_ t {{p}} Γ) zero = rename-NonVar
lookup-NonVar (t ,- Γ) (suc x) = rename-NonVar {{(lookup-NonVar Γ x)}}

--------------------------
-- P (head t) ⇒ Any P t --
--------------------------

-- For the usual `Any`, this would just be `here`. But if `t` is a backedge, then
-- we need to do some extra work.

head-rename : ∀ {X n} → (Γ : Scope X n) (t : Tree X n) {{_ : NonVar t}}
             → head Γ t ≡ head (t ,- Γ) (rename suc t)
head-rename Γ (step x t) = refl

head-rename-suc : ∀ {X n} (a b : Tree X n) {{_ : NonVar a}} {{_ : NonVar b}}
                 → (Γ : Scope X n) (t : Tree X n)
                 → head (a ,- Γ) (rename suc t) ≡ head (b ,- Γ) (rename suc t)
head-rename-suc a b Γ (step x t) = refl
head-rename-suc a b Γ (var x) = refl

head∘var≡head∘lookup : ∀ {X n} → (Γ : Scope X n) (x : Fin n)
                      → head Γ (var x) ≡  head Γ (lookup Γ x)
head∘var≡head∘lookup (t ,- Γ) zero =  head-rename Γ t
head∘var≡head∘lookup (t ,- Γ) (suc x) =
  begin
    head (t ,- Γ) (var (suc x))
  ≡⟨ head∘var≡head∘lookup Γ x ⟩
    head Γ (lookup Γ x)
  ≡⟨  head-rename Γ (lookup Γ x) {{lookup-NonVar Γ x}}   ⟩
    head _ (rename suc (lookup Γ x))
  ≡⟨  head-rename-suc (lookup Γ x) t {{lookup-NonVar Γ x}} Γ (lookup Γ x)  ⟩
    head (t ,- Γ) (lookup (t ,- Γ) (suc x))
  ∎ where open ≡-Reasoning


-- If we know that the tree is not a var, then `here` is easy.
here-NonVar : ∀ {X n x} {P : X → Set} (Γ : Scope X n) (t : Tree X n) {{_ : NonVar t}}
     → P x → x ≡ head Γ t → Any P Γ t
here-NonVar Γ (step x t) px refl = here px

-- P (head t) ⇒ Any P t
here-head : ∀ {X n x} {P : X → Set} {Γ : R.Scope X n} {t : R.Tree X n}
          → P x → x ≡ R.head Γ t → R.Any P Γ t
here-head {Γ = Γ} {R.step x t} p refl
  = R.here p
here-head {Γ = Γ} {R.var x} p refl
  = R.loop (here-NonVar Γ (lookup Γ x) ⦃ lookup-NonVar Γ x ⦄ p (head∘var≡head∘lookup Γ x))

-------------------------
-- Properties of `ext` --
-------------------------

-- ext-embed : ∀ {X n m} {s : Tree X n} {t : Tree X m} {{_ : NonVar s}} {{_ : NonVar t}}
--           → {Γ : Scope X n} {Δ : Scope X m} → (θ : Γ ⊑ Δ)
--           → (r : IsRenaming (erase θ) s t)
--           → embed' (inj θ r) ≗ ext (embed' θ)
-- ext-embed θ = ?

-- ext-embed-suc : ∀ {X n m} {s : Tree X n} {t : Tree X m} {{_ : NonVar s}} {{_ : NonVar t}}
--               → {Γ : Scope X n} {Δ : Scope X m} → (θ : Γ ⊑ Δ)
--               → (eq : rename (embed' θ) s ≡ t)
--               → ext (embed' (inj θ eq)) ∘ ext suc ≗ ext suc ∘ ext (embed' θ)
-- ext-embed-suc θ eq zero = refl
-- ext-embed-suc θ eq (suc x) = refl

----------------------------
-- Properties of Renaming --
----------------------------

rename-cong : ∀ {X n m} {ρ1 ρ2 : Rename n m} → ρ1 ≗ ρ2 → rename {X} ρ1 ≗ rename ρ2
rename-cong eq (step x leaf) = refl
rename-cong eq (step x (node1 op t))
  = cong (λ z → step x (node1 op z)) (rename-cong eq t)
rename-cong eq (step x (node2 op tl tr))
  = cong₂ (λ l r → step x (node2 op l r)) (rename-cong eq tl) (rename-cong eq tr)
rename-cong eq (step x (nodeη op t))
  = cong (λ z → step x (nodeη op z)) (rename-cong (ext-cong eq) t)
rename-cong eq (var x)
  = cong var (eq x)

rename-id : ∀ {X n} → rename {X} (id {A = Fin n}) ≗ id
rename-id (step x leaf) = refl
rename-id (step x (node1 op t)) = cong (λ a → step x (node1 op a)) (rename-id t)
rename-id (step x (node2 op tl tr)) = cong₂ (λ a b → step x (node2 op a b)) (rename-id tl) (rename-id tr)
rename-id (step x (nodeη op t)) = cong (λ a → step x (nodeη op a)) $
  begin
    rename (ext id) t
  ≡⟨ rename-cong ext-id t ⟩
    rename id t
  ≡⟨ rename-id t ⟩
    t
  ∎ where open ≡-Reasoning
rename-id (var x) = refl


rename-fusion : ∀ {At i j k} {ρ1 : Rename j k} {ρ2 : Rename i j} {ρ3 : Rename i k}
              → ρ1 ∘ ρ2 ≗ ρ3
              → (rename {At} ρ1) ∘ (rename ρ2) ≗ rename ρ3
rename-fusion eq (step x leaf) = refl
rename-fusion eq (step x (node1 op t)) = cong (λ z → step x (node1 op z)) (rename-fusion eq t)
rename-fusion eq (step x (node2 op tl tr)) = cong₂ (λ u v → step x (node2 op u v)) (rename-fusion eq tl) (rename-fusion eq tr)
rename-fusion eq (step x (nodeη op t)) = cong (λ z → step x (nodeη op z)) (rename-fusion (ext-fusion eq) t)
rename-fusion eq (var x) = cong var (eq x)

-- renaming by `suc` commutes with arbitrary renamings via `ext`
rename-ext : ∀ {At i j} (ρ : Rename i j)
            → rename {At} suc ∘ rename ρ ≗ rename (ext ρ) ∘ rename suc
rename-ext ρ t =
  begin
    (rename F.suc ∘ rename ρ) t
  ≡⟨ rename-fusion (λ _ → refl) t ⟩
    rename (F.suc ∘ ρ) t
  ≡⟨ rename-cong (λ _ → refl) t ⟩
    rename (ext ρ ∘ F.suc) t
  ≡⟨ (sym $ rename-fusion (λ _ → refl) t) ⟩
    (rename (ext ρ) ∘ rename F.suc) t
  ∎ where open ≡-Reasoning

-----------------------
-- Properties of _⊑_ --
-----------------------

forget : ∀ {X n m} {Γ : Scope X n} {Δ : Scope X m} → Γ ⊑ Δ → Thin n m
forget end = end
forget (inj θ _) = inj (forget θ)
forget (pad θ) = pad (forget θ)

t,Γ⋢Γ : ∀ {X n m} {Γ : Scope X n} {Δ : Scope X m} → ¬ (Thin n m) → ¬ (Γ ⊑ Δ)
t,Γ⋢Γ ¬θ θ = ¬θ (forget θ)

embed'-id : ∀ {X n} {Γ : Scope X n} (θ : Γ ⊑ Γ) → embed' θ ≗ id
embed'-id (inj θ eq) zero = refl
embed'-id (inj θ eq) (suc x) = cong suc (embed'-id θ x)
embed'-id (pad θ) x = ⊥-elim (t,Γ⋢Γ 1+n≰n θ)

⊑-refl : ∀ {X n} {Γ : Scope X n} → Γ ⊑ Γ
⊑-refl {X} {n} {[]} = end
⊑-refl {X} {n} {t ,- Γ} = {!!}

-- ⊑-refl {X} {n} {t ,- Γ} = inj ⊑-refl $
--   begin
--     rename (embed' ⊑-refl) t
--   ≡⟨ rename-cong (embed'-id {Γ = Γ} ⊑-refl) t ⟩
--     rename id t
--   ≡⟨ rename-id t ⟩
--     t
--   ∎ where open ≡-Reasoning


-------------------------
-- Properties of `Any` --
-------------------------

-- Structural equality of trees
data TreeEq {X : Set} {n m : ℕ} {Γ : Scope X n} {Δ : Scope X m} (θ : Γ ⊑ Δ)
  : Tree X n → Tree X m → Set
data TreeEq-step {X : Set} {n m : ℕ} {Γ : Scope X n} {Δ : Scope X m} (θ : Γ ⊑ Δ) {x y : X} (x≡y : x ≡ y)
  : Tree-step X n → Tree-step X m → Set

data TreeEq {X} {n} {m} {Γ} {Δ} θ where
  step : {x y : X} → (x≡y : x ≡ y)
       → {tx : Tree-step X n} {ty : Tree-step X m} → TreeEq-step θ x≡y tx ty
       → TreeEq θ (step x tx) (step y ty)

  var : {x : Fin n} {y : Fin m} → embed' θ x ≡ y
      → TreeEq θ (var x) (var y)

data TreeEq-step {X} {n} {m} {Γ} {Δ} θ {x} {y} x≡y where
  leaf : TreeEq-step θ x≡y leaf leaf

  node1 : ∀ op → {tx : Tree X n} {ty : Tree X m}
        → TreeEq θ tx ty
        → TreeEq-step θ x≡y (node1 op tx) (node1 op ty)

  node2 : ∀ op → {txl txr : Tree X n} {tyl tyr : Tree X m}
        → TreeEq θ txl tyl → TreeEq θ txr tyr
        → TreeEq-step θ x≡y (node2 op txl txr) (node2 op tyl tyr)

  nodeη : ∀ op → {tx : Tree X (suc n)} {ty : Tree X (suc m)}
        → {tγ : Tree X n} {tδ : Tree X m} {{nvtγ : NonVar tγ}} {{nvtδ : NonVar tδ}}
        → (r : IsRenaming (erase θ) tγ tδ)
        → TreeEq {X} {suc n} {suc m} {Γ = tγ ,- Γ} {Δ = tδ ,- Δ} (inj θ r) tx ty
        → TreeEq-step θ x≡y (nodeη op tx) (nodeη op ty)

rename-TreeEq : ∀ {X n m} {Γ : Scope X n} {Δ : Scope X m}
              → (θ : Γ ⊑ Δ) → (t : Tree X n)
              → TreeEq θ t (rename (embed' θ) t)
rename-TreeEq θ (var x) = {!!}
rename-TreeEq θ (step x leaf)
  = step refl leaf
rename-TreeEq θ (step x (node1 op t))
  = step refl (node1 op (rename-TreeEq θ t))
rename-TreeEq θ (step x (node2 op tl tr))
  = step refl (node2 op (rename-TreeEq θ tl) (rename-TreeEq θ tr))
rename-TreeEq θ (step x (nodeη op t))
  = {!!}

--   = step refl (nodeη op refl (subst (TreeEq (inj θ refl) t)
--                                     (rename-cong (ext-embed θ refl) t)
--                                     (rename-TreeEq (inj {s = step x (nodeη op t)} θ refl) t)))
-- rename-TreeEq θ (var x)
--   = var refl


TreeEq-rename-inj' : ∀ {X n m} {Γ : Scope X n} {Δ : Scope X m}
                  → {tx : Tree X n} {ty : Tree X m}
                  → {tx' : Tree X (suc n)} {ty' : Tree X (suc m)}
                  → {tγ : Tree X n} {tδ : Tree X m} {{nvtγ : NonVar tγ}} {{nvtδ : NonVar tδ}}
                  → (θ : Γ ⊑ Δ)
                  → {σ1 : Thin n (suc n)} {σ2 : Thin m (suc m)}
                  → IsRenaming σ1 tx tx' → IsRenaming σ2 ty ty'
                  → Ext σ1 σ2
                  → (r : IsRenaming (erase θ) tγ  tδ)
                  → TreeEq θ tx ty → TreeEq (inj θ r) tx' ty'
TreeEq-rename-inj' θ (step {a} refl leaf) (step refl leaf) ex eq (step refl leaf)
  = step refl leaf
TreeEq-rename-inj' θ (step {a} refl (node1 .op x)) (step refl (node1 .op x₁)) ex eq (step refl (node1 op x₂))
  = step refl (node1 op (TreeEq-rename-inj' θ x x₁ ex eq x₂))
TreeEq-rename-inj' θ (step {a} refl (node2 .op x x₁)) (step refl (node2 .op x₂ x₃)) ex eq (step refl (node2 op x₄ x₅))
  = step refl (node2 op (TreeEq-rename-inj' θ x x₂ ex eq x₄) (TreeEq-rename-inj' θ x₁ x₃ ex eq x₅))
TreeEq-rename-inj' {X} {n} {m} {Γ} {Δ} {.step a (nodeη op tx)} {.step a (nodeη op ty)} {.step a (nodeη op tx')} {.step a (nodeη op ty')} {tγ = tγ} {tδ = tδ} {{nvtγ}} {{nvtδ}} θ {σ1} {σ2} (step {a} refl (nodeη .op sx)) (step refl (nodeη .op sy)) ex eq1 (step refl (nodeη op {tγ = tγ'} {tδ = tδ'} eq2 teq))
  = step refl (nodeη op {tx'} {ty'} {step a (nodeη op tx')} {step a (nodeη op ty')} ⦃ step ⦄ ⦃ step ⦄
                     {!!}
                     (TreeEq-rename-inj' {X} {suc n} {suc m} {tγ ,- Γ} {tδ ,- Δ} {tx} {ty}
                       {tx'} {ty'} {step a (nodeη op tx')} {step a (nodeη op ty')} ⦃ step ⦄ ⦃ step ⦄ (inj θ eq1) {inj σ1} {inj σ2} sx sy
                       (inj ex) _ {!eq1 and eq2 (and hence tγ/tγ' and tδ/tδ') being different is the problem - need to be able to stick teq into here!}))
TreeEq-rename-inj' θ {σ1} {σ2} (var p) (var q) ex eq (var r)
  = var (trans (trans {!!} (cong (embed σ2) r)) q)

TreeEq-rename-inj : ∀ {X n m} {Γ : Scope X n} {Δ : Scope X m}
                  → {tx : Tree X n} {ty : Tree X m}
                  → {tγ : Tree X n} {tδ : Tree X m} {{nvtγ : NonVar tγ}} {{nvtδ : NonVar tδ}}
                  → (θ : Γ ⊑ Δ)
                  → (r : IsRenaming (erase θ) tγ tδ)
                  → TreeEq θ tx ty → TreeEq (inj θ r) (rename suc tx) (rename suc ty)
TreeEq-rename-inj θ eq p = {!!}


{-

TreeEq-rename-pad : ∀ {X n m} {Γ : Scope X n} {Δ : Scope X m}
                  → {tx : Tree X n} {ty : Tree X m}
                  → {tδ : Tree X m} {{nvtδ : NonVar tδ}}
                  → (θ : Γ ⊑ Δ)
                  → TreeEq θ tx ty → TreeEq (pad {t = tδ} θ) tx (rename suc ty)
TreeEq-rename-pad θ (step x≡y leaf)
  = step x≡y leaf
TreeEq-rename-pad θ (step x≡y (node1 op eq))
  = step x≡y (node1 op (TreeEq-rename-pad θ eq))
TreeEq-rename-pad θ (step x≡y (node2 op eql eqr))
  = step x≡y (node2 op (TreeEq-rename-pad θ eql) (TreeEq-rename-pad θ eqr))
TreeEq-rename-pad {X} {n} {m} {Γ} {Δ} {step x (nodeη op tx)} {step y (nodeη op ty)} {tδ} θ (step {x = x} {y} x≡y (nodeη op eq' eq))
  = step x≡y (nodeη op {!!} {!TreeEq-rename-pad ? eq  !}) where
  lem : ∀ {X n} {x y : X} {u : Tree X (suc n)} {v : Tree X (suc n)}
      → x ≡ y → _≡_ {A = Tree X n} (step x (nodeη op u)) (step y (nodeη op v))
      → u ≡ v
  lem refl refl = refl

  -- lem2 : rename (ext (λ x₁ → suc (embed' θ x₁))) tx ≡ rename (ext suc) ty
  -- lem2 =
  --   begin
  --     rename (ext (λ x₁ → suc (embed' θ x₁))) tx
  --   ≡⟨ rename-fusion (ext-fusion (λ _ → refl)) tx ⟨
  --     rename (ext suc) (rename (ext (embed' θ)) tx)
  --   ≡⟨ cong (rename $ ext suc) (lem x≡y eq') ⟩
  --     rename (ext suc) ty
  --   ∎ where open ≡-Reasoning

TreeEq-rename-pad θ (var eq) = var (cong suc eq)

-- Lookups are equal as long as the thinning equalises the two variables.
lookup-TreeEq : ∀ {X n m} {Γ : Scope X n} {Δ : Scope X m} {x : Fin n} {y : Fin m}
             → (θ : Γ ⊑ Δ)
             → embed' θ x ≡ y
             → TreeEq θ (lookup Γ x) (lookup Δ y)
lookup-TreeEq {x = zero}  (inj θ refl) refl = TreeEq-rename-inj θ refl (rename-TreeEq θ _)
lookup-TreeEq {x = suc x} (inj θ refl) refl = TreeEq-rename-inj θ refl (lookup-TreeEq θ refl)
lookup-TreeEq {x = zero}  (pad θ) refl      = TreeEq-rename-pad θ (lookup-TreeEq θ refl)
lookup-TreeEq {x = suc x} (pad θ) refl      = TreeEq-rename-pad θ (lookup-TreeEq θ refl)

mutual
  any-subst : ∀ {X n m} {P : X → Set}
            → {Γ : Scope X n} {Δ : Scope X m} {tx : Tree X n} {ty : Tree X m}
            → (θ : Γ ⊑ Δ)
            → TreeEq θ tx ty
            → Any P Γ tx → Any P Δ ty
  any-subst θ (step x≡y eq) (here px) = here (subst _ x≡y px)
  any-subst θ (step x≡y eq) (step ptx) = step (any-subst-step x≡y θ eq ptx)
  any-subst θ (var eq) (loop ptx) = loop (any-subst θ (lookup-TreeEq θ eq) ptx)

  any-subst-step : ∀ {X n m} {P : X → Set}
                 → {x y : X} → (x≡y : x ≡ y)
                 → {Γ : Scope X n} {Δ : Scope X m} {tx : Tree-step X n} {ty : Tree-step X m}
                 → (θ : Γ ⊑ Δ)
                 → TreeEq-step θ x≡y tx ty
                 → Any-step P x Γ tx → Any-step P y Δ ty
  any-subst-step x≡y θ leaf leaf = leaf
  any-subst-step x≡y θ (node1 op eq) (node1 ptx) = node1 (any-subst θ eq ptx)
  any-subst-step x≡y θ (node2 op eql eqr) (node2l ptx) = node2l (any-subst θ eql ptx)
  any-subst-step x≡y θ (node2 op eql eqr) (node2r ptx) = node2r (any-subst θ eqr ptx)
  any-subst-step x≡y θ (nodeη op eq' eq) (nodeη ptx) = nodeη (any-subst (inj θ {!!}) {!!} ptx)




-- If we have some proof of Any, then padding out the scope doesn't change the proof. It's still the same
-- path, just with different indices.
any-rename : ∀ {X n m} {P : X → Set} {Γ : Scope X n} {Δ : Scope X m} {t : Tree X n}
            → (θ : Γ ⊑ Δ) -- Γ embeds into Δ
            → Any P Γ t → Any P Δ (rename (embed' θ) t)
any-rename θ = any-subst θ (rename-TreeEq θ _)


-- Can't directly prove this, because `suc` will become `ext suc` after traversing a binder.
-- Need to do something more general.
any-rename-suc : ∀ {X n} {P : X → Set} {Γ : Scope X n} {t : Tree X n}
                → {s : Tree X n} {{nvs : NonVar s}}
                → Any P Γ t → Any P (s ,- Γ) (rename suc t)
any-rename-suc {n = n} {P} {Γ} {t} {s} pt
  = subst (Any P (s ,- Γ))
          (rename-cong (λ x → cong suc (embed'-id ⊑-refl x)) t)
          (any-rename {Γ = Γ} {Δ = s ,- Γ} {t} (pad ⊑-refl) pt)

---------------------------------------------------
-- `Any` for R-trees and NWF-trees is equivalent --
---------------------------------------------------

-- NWF to Rational
∞bisim-unfold-eventually→ : ∀ {X n} {P : X → Set}
                         → {t : ∞NWFTree X} {rt : R.Tree X n} {Γ : R.Scope X n}
                         → t ~ R.unfold Γ rt
                         → NWF.Any P t
                         → R.Any P Γ rt

bisim-unfold-eventually→ : ∀ {X n} {P : X → Set}
                        → {t : NWFTree X} {rt : R.Tree X n} {Γ : R.Scope X n}
                        → NWF.Pointwise _≡_ t (R.unfold-subtree Γ rt)
                        → NWF.Any-step P t
                        → R.Any P Γ rt

∞bisim-unfold-eventually→ rs (here px) = here-head px (rs .NWF.head)
∞bisim-unfold-eventually→ rs (there pt) = bisim-unfold-eventually→ (rs .NWF.tree) pt

bisim-unfold-eventually→ {rt = step x leaf} NWF.leaf ()
bisim-unfold-eventually→ {rt = step x (node1 op rt)} (NWF.node1 rs) (NWF.node1 pt)
  = step (node1 (∞bisim-unfold-eventually→ rs pt))
bisim-unfold-eventually→ {rt = step x (node2 op rtl rtr)} (NWF.node2 rsl rsr) (NWF.node2l pt)
  = step (node2l (∞bisim-unfold-eventually→ rsl pt))
bisim-unfold-eventually→ {rt = step x (node2 op rtl rtr)} (NWF.node2 rsl rsr) (NWF.node2r pt)
  = step (node2r (∞bisim-unfold-eventually→ rsr pt))
bisim-unfold-eventually→ {rt = step x (nodeη op rt)} (NWF.nodeη rs) (NWF.nodeη pt)
  = step (nodeη (∞bisim-unfold-eventually→ rs pt))
bisim-unfold-eventually→ {rt = var zero} {t ,- Γ} rs pt
  = loop (any-rename-suc (bisim-unfold-eventually→ {rt = t} {Γ = Γ} rs pt))
bisim-unfold-eventually→ {rt = var (suc x)} {t ,- Γ} rs pt
  = any-rename-suc (bisim-unfold-eventually→ {rt = var x} {Γ} rs pt)

{-
-- Rational to NWF (not needed rn)
∞bisim-unfold-eventually← : ∀ {X n} {P : X → Set}
                         → {t : ∞NWFTree X} {rt : R.Tree X n} {Γ : R.Scope X n}
                         → t ~ R.unfold Γ rt
                         → R.Any P Γ rt
                         → NWF.Any P t
-}

-}
