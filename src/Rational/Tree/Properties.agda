{-# OPTIONS --safe --guardedness --with-K #-}
module Rational.Tree.Properties where

open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Fin as F using (Fin; zero; suc)
open import Data.Fin.Renaming
open import Data.Nat
open import Data.Empty
open import Data.Thinning as Th hiding (id)
open import MuCalc.Base using (Op₁; Op₂; Opη)
open import Codata.NWFTree as NWF using (∞NWFTree; NWFTree; _~_; here; there)
open import Rational.Tree as R
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

ext-embed : ∀ {X n m} {s : Tree X n} {t : Tree X m} {{_ : NonVar s}} {{_ : NonVar t}}
          → {Γ : Scope X n} {Δ : Scope X m} → (θ : Γ ⊑ Δ)
          → (r : IsRenaming (embed' θ) s t)
          → embed' (inj θ r) ≗ ext (embed' θ)
ext-embed θ r zero = refl
ext-embed θ r (suc x) = refl

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

rename-IsRenaming : ∀ {X n m} {ρ : Rename n m} {tx : Tree X n} {ty : Tree X m}
                  → rename ρ tx ≡ ty
                  → IsRenaming ρ tx ty
rename-IsRenaming {tx = step x leaf} refl = step refl leaf
rename-IsRenaming {tx = step x (node1 op t)} refl = step refl (node1 op (rename-IsRenaming refl))
rename-IsRenaming {tx = step x (node2 op tl tr)} refl = step refl (node2 op (rename-IsRenaming refl) (rename-IsRenaming refl))
rename-IsRenaming {tx = step x (nodeη op t)} refl = step refl (nodeη op (rename-IsRenaming refl))
rename-IsRenaming {tx = var x} refl = var refl

IsRenaming→≡ : ∀ {X n m} {ρ : Rename n m} {tx : Tree X n} {ty : Tree X m}
             → IsRenaming ρ tx ty
             → rename ρ tx ≡ ty
IsRenaming→≡ (step refl leaf) = refl
IsRenaming→≡ (step refl (node1 op p)) = cong (λ z → step _ (node1 op z)) (IsRenaming→≡ p)
IsRenaming→≡ (step refl (node2 op p q)) = cong₂ (λ z1 z2 → step _ (node2 op z1 z2)) (IsRenaming→≡ p) (IsRenaming→≡ q)
IsRenaming→≡ (step refl (nodeη op p)) = cong (λ z → step _ (nodeη op z)) (IsRenaming→≡ p)
IsRenaming→≡ (var p) = cong var p

rename-embed-inj : ∀ {X} {n m}
                 → {ρ : Rename n m} {tx : Tree X n} {ty : Tree X m}
                 → rename ρ tx ≡ ty
                 → rename (ext ρ) (rename suc tx) ≡ rename suc ty
rename-embed-inj {ρ = ρ} {tx} refl = sym $ rename-ext ρ tx


-- Thinning preserves lookup.
rename-lookup : ∀ {X} {n m} {Γ : Scope X n} {Δ : Scope X m}
              → (θ : Γ ⊑ Δ) (x : Fin n) {y : Fin m}
              → embed' θ x ≡ y
              → IsRenaming (embed' θ) (lookup Γ x) (lookup Δ y)
rename-lookup (inj {s = s} {t = t} θ p) zero refl = rename-IsRenaming $
  begin
    rename (embed' (inj θ p)) (rename suc s)
  ≡⟨ rename-cong (ext-embed θ p) (rename suc s) ⟩
    rename (ext (embed' θ)) (rename suc s)
  ≡⟨ rename-embed-inj (IsRenaming→≡ p) ⟩
    rename suc t
  ∎ where open ≡-Reasoning
rename-lookup {Γ = tγ ,- Γ} {Δ = tδ ,- Δ} (inj θ p) (suc x) refl = rename-IsRenaming $
  begin
    rename (embed' (inj θ p)) (lookup (tγ ,- Γ) (suc x))
  ≡⟨ rename-cong (ext-embed θ p) (rename suc (lookup Γ x)) ⟩
    rename (ext (embed' θ)) (rename suc (lookup Γ x))
  ≡⟨ rename-embed-inj (IsRenaming→≡ (rename-lookup θ x refl)) ⟩
    rename suc (lookup Δ (embed' θ x))
  ∎ where open ≡-Reasoning
rename-lookup {Γ = Γ} {Δ = tδ ,- Δ} (pad θ) x refl = rename-IsRenaming $
  begin
    rename (suc ∘ (embed' θ)) (lookup Γ x)
  ≡⟨ rename-fusion (λ _ → refl) (lookup Γ x) ⟨
    rename (ext (embed' θ)) (rename suc (lookup Γ x))
  ≡⟨ rename-embed-inj $ IsRenaming→≡ $ rename-lookup θ x refl ⟩
    rename suc (lookup Δ (embed' θ x))
  ∎ where open ≡-Reasoning

IsRenaming-subst : ∀ {X n m} {ρ1 ρ2 : Rename n m} {tx : Tree X n} {ty : Tree X m}
                 → ρ1 ≗ ρ2
                 → IsRenaming ρ1 tx ty → IsRenaming ρ2 tx ty
IsRenaming-subst eq (step refl leaf) = step refl leaf
IsRenaming-subst eq (step refl (node1 op x)) = step refl (node1 op (IsRenaming-subst eq x))
IsRenaming-subst eq (step refl (node2 op x x₁)) = step refl
                                                   (node2 op (IsRenaming-subst eq x) (IsRenaming-subst eq x₁))
IsRenaming-subst eq (step refl (nodeη op x)) = step refl (nodeη op (IsRenaming-subst (ext-cong eq) x))
IsRenaming-subst eq (var x) = var (trans (sym $ eq _) x)


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
⊑-refl {X} {n} {t ,- Γ} = inj ⊑-refl $ rename-IsRenaming $
  begin
    rename (embed' ⊑-refl) t
  ≡⟨ rename-cong (embed'-id ⊑-refl) t ⟩
    rename id t
  ≡⟨ rename-id t ⟩
    id t
  ∎ where open ≡-Reasoning



-------------------------
-- Properties of `Any` --
-------------------------

mutual
  any-subst : ∀ {X n m} {P : X → Set}
            → {Γ : Scope X n} {Δ : Scope X m} {tx : Tree X n} {ty : Tree X m}
            → (θ : Γ ⊑ Δ)
            → IsRenaming (embed' θ) tx ty
            → Any P Γ tx → Any P Δ ty
  any-subst θ (step x≡y eq) (here px) = here (subst _ x≡y px)
  any-subst θ (step x≡y eq) (step ptx) = step (any-subst-step x≡y θ eq ptx)
  any-subst θ (var eq) (loop ptx) = loop (any-subst θ (rename-lookup θ _ eq) ptx)

  any-subst-step : ∀ {X n m} {P : X → Set}
                 → {x y : X} → (x≡y : x ≡ y)
                 → {Γ : Scope X n} {Δ : Scope X m} {tx : Tree-step X n} {ty : Tree-step X m}
                 → (θ : Γ ⊑ Δ)
                 → IsRenaming-step (embed' θ) tx ty
                 → Any-step P x Γ tx → Any-step P y Δ ty
  any-subst-step x≡y θ (node1 op eq) (node1 ptx) = node1 (any-subst θ eq ptx)
  any-subst-step x≡y θ (node2 op eql eqr) (node2l ptx) = node2l (any-subst θ eql ptx)
  any-subst-step x≡y θ (node2 op eql eqr) (node2r ptx) = node2r (any-subst θ eqr ptx)
  any-subst-step {x = x} {y} x≡y θ (nodeη op eq) (nodeη ptx)
    = nodeη (any-subst (inj θ (step x≡y (nodeη op eq))) (IsRenaming-subst (sym ∘ ext-embed θ (step x≡y (nodeη op eq))) eq) ptx)




-- If we have some proof of Any, then padding out the scope doesn't change the proof. It's still the same
-- path, just with different indices.
any-rename : ∀ {X n m} {P : X → Set} {Γ : Scope X n} {Δ : Scope X m} {t : Tree X n}
            → (θ : Γ ⊑ Δ) -- Γ embeds into Δ
            → Any P Γ t → Any P Δ (rename (embed' θ) t)
any-rename θ = any-subst θ (rename-IsRenaming refl)

-- Couldn't directly prove this, because `suc` will become `ext suc` after traversing a binder.
-- But it is an instance of any-rename:
any-rename-suc : ∀ {X n} {P : X → Set} {Γ : Scope X n} {t : Tree X n}
                → {s : Tree X n} {{nvs : NonVar s}}
                → Any P Γ t → Any P (s ,- Γ) (rename suc t)
any-rename-suc {n = n} {P} {Γ} {t} {s} pt
  = let pt' = any-rename {Γ = Γ} {Δ = s ,- Γ} {t} (pad ⊑-refl) pt
    in subst (Any P (s ,- Γ)) (rename-cong (λ x → cong suc (embed'-id ⊑-refl x)) t) pt'



-----------------------------
-- Properties of Unfolding --
-----------------------------

head-rename-suc' : ∀ {X n} (tγ : Tree X n) {{nvtγ : NonVar tγ}} (Γ : Scope X n) (t : Tree X n)
                 → head Γ t ≡ head (tγ ,- Γ) (rename suc t)
head-rename-suc' tγ Γ (step x t) = refl
head-rename-suc' tγ Γ (var x) = refl

head-lookup : ∀ {X n} (Γ : Scope X n) (x : Fin n) → head Γ (var x) ≡ head Γ (lookup Γ x)
head-lookup (t ,- Γ) zero = head-rename-suc' t Γ t
head-lookup (t ,- Γ) (suc x) =
  begin
    head (t ,- Γ) (var (suc x))
  ≡⟨ head-lookup Γ x ⟩
    head Γ (lookup Γ x)
  ≡⟨ head-rename-suc' t Γ (lookup Γ x) ⟩
    head (t ,- Γ) (lookup (t ,- Γ) (suc x))
  ∎ where open ≡-Reasoning

-- If two trees are equivalent, then they have the same head.
eq-head : ∀ {X n m} {Γ : Scope X n} {Δ : Scope X m}
        → (θ : Γ ⊑ Δ)
        → {tx : Tree X n} {ty : Tree X m}
        → IsRenaming (embed' θ) tx ty
        → head Γ tx ≡ head Δ ty
eq-head θ (step x≡y _) = x≡y
eq-head (inj θ eq) (var {zero} refl) = eq-head θ eq
eq-head (inj θ eq1) (var {suc x} refl) = eq-head θ (var refl)
eq-head (pad θ) (var refl) = eq-head θ (var refl)


-- The key lemma for bisimulations of unfoldings; if the trees are equivalent, then their unfoldings
-- are bisimilar.
-- TODO: The reverse is probably also true?
mutual
  unfold-bisim : ∀ {X n m} {Γ : Scope X n} {Δ : Scope X m}
               → (θ : Γ ⊑ Δ)
               → {tx : Tree X n} {ty : Tree X m}
               → IsRenaming (embed' θ) tx ty
               → unfold Γ tx ~ unfold Δ ty
  unfold-bisim θ eq .NWF.head = eq-head θ eq
  unfold-bisim θ eq .NWF.tree = unfold-bisim-step θ eq

  unfold-bisim-step : ∀ {X n m} {Γ : Scope X n} {Δ : Scope X m}
                    → (θ : Γ ⊑ Δ)
                    → {tx : Tree X n} {ty : Tree X m}
                    → IsRenaming (embed' θ) tx ty
                    → NWF.Pointwise _≡_ (unfold-subtree Γ tx) (unfold-subtree Δ ty)
  unfold-bisim-step θ (step x≡y leaf)
    = NWF.leaf
  unfold-bisim-step θ (step x≡y (node1 op eq))
    = NWF.node1 (unfold-bisim θ eq)
  unfold-bisim-step θ (step x≡y (node2 op eql eqr))
    = NWF.node2 (unfold-bisim θ eql) (unfold-bisim θ eqr)
  unfold-bisim-step {Γ = Γ} {Δ} θ tx@{step x (nodeη op tx')} ty@{step y (nodeη op ty')} eq'@(step {x = x} {y} x≡y (nodeη op eq))
    = NWF.nodeη (unfold-bisim (inj θ eq') (IsRenaming-subst (sym ∘ ext-embed θ _) eq))
  unfold-bisim-step (inj θ eq1) {var zero} (var refl) = unfold-bisim-step θ eq1
  unfold-bisim-step (inj θ eq1) {var (suc x)} (var refl) = unfold-bisim-step θ (var refl)
  unfold-bisim-step (pad θ) (var refl) = unfold-bisim-step θ (var refl)


unfold-rename-suc : ∀ {X n} (tγ : Tree X n) {{nvtγ : NonVar tγ}} (Γ : Scope X n) (t : Tree X n)
                  → unfold Γ t ~ unfold (tγ ,- Γ) (rename suc t)
unfold-rename-suc tγ Γ t
  = unfold-bisim (pad ⊑-refl)
                 (rename-IsRenaming (rename-cong (λ x → cong suc (embed'-id ⊑-refl x)) t))

mutual
  unfold-lookup : ∀ {X n} (Γ : Scope X n) (x : Fin n)
                → unfold Γ (var x) ~ unfold Γ (lookup Γ x)
  unfold-lookup Γ x .NWF.head = head-lookup Γ x
  unfold-lookup Γ x .NWF.tree = unfold-lookup-step Γ x

  unfold-lookup-step : ∀ {X n} (Γ : Scope X n) (x : Fin n)
                     → NWF.Pointwise _≡_ (unfold-subtree Γ (var x)) (unfold-subtree Γ (lookup Γ x))
  unfold-lookup-step (step x leaf ,- Γ) zero
    = NWF.leaf
  unfold-lookup-step (step x (node1 op t) ,- Γ) zero
    = NWF.node1 (unfold-rename-suc (step x (node1 op t)) Γ t)
  unfold-lookup-step (step x (node2 op tl tr) ,- Γ) zero
    = NWF.node2 (unfold-rename-suc (step x (node2 op tl tr)) Γ tl)
                (unfold-rename-suc (step x (node2 op tl tr)) Γ tr)
  unfold-lookup-step (step x (nodeη op t) ,- Γ) zero
    = NWF.nodeη {!unfold-rename-suc!}
  unfold-lookup-step {X} (t ,- Γ) (suc x)
    = run-tree (`map-trans (`map-lift $ unfold-lookup-step Γ x)
                           (`map-lift $ NWF.tree $ unfold-rename-suc t Γ (lookup Γ x)))
    where open NWF.bisim-Reasoning X


---------------------------------------------------
-- `Any` for R-trees and NWF-trees is equivalent --
---------------------------------------------------


-- NWF to Rational
mutual
  ∞bisim-unfold-any→ : ∀ {X n} {P : X → Set}
                     → {t : ∞NWFTree X} {rt : R.Tree X n} {Γ : R.Scope X n}
                     → t ~ R.unfold Γ rt
                     → NWF.Any P t
                     → R.Any P Γ rt
  ∞bisim-unfold-any→ rs (here px) = here-head px (rs .NWF.head)
  ∞bisim-unfold-any→ rs (there pt) = bisim-unfold-any→ (rs .NWF.tree) pt


  bisim-unfold-any→ : ∀ {X n} {P : X → Set}
                    → {t : NWFTree X} {rt : R.Tree X n} {Γ : R.Scope X n}
                    → NWF.Pointwise _≡_ t (R.unfold-subtree Γ rt)
                    → NWF.Any-step P t
                    → R.Any P Γ rt
  bisim-unfold-any→ {rt = step x leaf} NWF.leaf ()
  bisim-unfold-any→ {rt = step x (node1 op rt)} (NWF.node1 rs) (NWF.node1 pt)
    = step (node1 (∞bisim-unfold-any→ rs pt))
  bisim-unfold-any→ {rt = step x (node2 op rtl rtr)} (NWF.node2 rsl rsr) (NWF.node2l pt)
    = step (node2l (∞bisim-unfold-any→ rsl pt))
  bisim-unfold-any→ {rt = step x (node2 op rtl rtr)} (NWF.node2 rsl rsr) (NWF.node2r pt)
    = step (node2r (∞bisim-unfold-any→ rsr pt))
  bisim-unfold-any→ {rt = step x (nodeη op rt)} (NWF.nodeη rs) (NWF.nodeη pt)
    = step (nodeη (∞bisim-unfold-any→ rs pt))
  bisim-unfold-any→ {rt = var zero} {t ,- Γ} rs pt
    = loop (any-rename-suc (bisim-unfold-any→ {rt = t} {Γ = Γ} rs pt))
  bisim-unfold-any→ {rt = var (suc x)} {t ,- Γ} rs pt
    = any-rename-suc (bisim-unfold-any→ {rt = var x} {Γ} rs pt)


-- Rational to NWF
mutual
  ∞bisim-unfold-any← : ∀ {X n} {P : X → Set}
                           → {t : ∞NWFTree X} {rt : R.Tree X n} {Γ : R.Scope X n}
                           → t ~ R.unfold Γ rt
                           → R.Any P Γ rt
                           → NWF.Any P t
  ∞bisim-unfold-any← {P = P} rs (here px)
    = here (subst P (sym $ NWF.head rs) px)
  ∞bisim-unfold-any← rs (step px)
    = there (bisim-unfold-any← (NWF.tree rs) px)
  ∞bisim-unfold-any← {Γ = Γ} rs (loop {x = x} px)
    = ∞bisim-unfold-any← (NWF.~-trans rs (unfold-lookup Γ x)) px


  bisim-unfold-any← : ∀ {X n x} {P : X → Set}
                    → {t : NWFTree X} {rt : R.Tree-step X n} {Γ : R.Scope X n}
                    → NWF.Pointwise _≡_ t (unfold-subtree Γ (step x rt))
                    → R.Any-step P x Γ rt
                    → NWF.Any-step P t
  bisim-unfold-any← {rt = node1 op t} (NWF.node1 rs) (node1 px)
    = NWF.node1 (∞bisim-unfold-any← rs px)
  bisim-unfold-any← {rt = node2 op tl tr} (NWF.node2 rsl rsr) (node2l px)
    = NWF.node2l (∞bisim-unfold-any← rsl px)
  bisim-unfold-any← {rt = node2 op tl tr} (NWF.node2 rsl rsr) (node2r px)
    = NWF.node2r (∞bisim-unfold-any← rsr px)
  bisim-unfold-any← {rt = nodeη op t} (NWF.nodeη rs) (nodeη px)
    = NWF.nodeη (∞bisim-unfold-any← rs px)
