{-# OPTIONS --safe --guardedness #-}
module Rational.Tree.Properties where

open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Fin
open import MuCalc.Base using (Op₁; Op₂; Opη)
open import Codata.NWFTree as NWF
open import Rational.Tree as R using ()

------------------------------------------------------------------------------
-- Unfolding a Variable and Unfolding a `lookup` take you to the same place --
------------------------------------------------------------------------------

head-rescope : ∀ {X n} → (Γ : R.Scope X n) (t : R.Tree X n) (s : R.Tree X n) {{_ : R.NonVar s}}
             → R.head (s R.,- Γ) (R.rescope suc t) ≡ R.head Γ t
head-rescope Γ (R.loop x) s = refl
head-rescope Γ (R.leaf x) s = refl
head-rescope Γ (R.node1 x x₁ t) s = refl
head-rescope Γ (R.node2 x x₁ t t₁) s = refl
head-rescope Γ (R.nodeη x x₁ t) s = refl

unfold-loop-lookup-head : ∀ {X n} → (Γ : R.Scope X n) (x : Fin n)
                        → R.head Γ (R.lookup Γ x) ≡ R.head Γ (R.loop x)
unfold-loop-lookup-head (t R.,- Γ) zero = head-rescope Γ t t
unfold-loop-lookup-head (t R.,- Γ) (suc x) =
  begin
    R.head (t R.,- Γ) (R.lookup (t R.,- Γ) (suc x))
  ≡⟨ head-rescope Γ (R.lookup Γ x) t ⟩
    R.head Γ (R.lookup Γ x)
  ≡⟨ unfold-loop-lookup-head Γ x ⟩
    R.head (t R.,- Γ) (R.loop (suc x))
  ∎ where open ≡-Reasoning

unfold-loop-lookup : ∀ {X n} → (Γ : R.Scope X n) (x : Fin n)
                   → R.unfold Γ (R.lookup Γ x) ~ R.unfold Γ (R.loop x)

unfold-loop-lookup-tree : ∀ {X n} → (Γ : R.Scope X n) (x : Fin n)
                        → Pointwise _≡_ (R.tree Γ (R.lookup Γ x)) (R.tree Γ (R.loop x))

unfold-loop-lookup Γ x .head = unfold-loop-lookup-head Γ x
unfold-loop-lookup Γ x .tree = unfold-loop-lookup-tree Γ x

unfold-loop-lookup-tree (t R.,- Γ) zero = {!!}
unfold-loop-lookup-tree (t R.,- Γ) (suc x) = {!!}

--------------------------------------------------------
-- Eventually for R-trees and NWF-trees is equivalent --
--------------------------------------------------------

-- NWF to Rational
∞bisim-unfold-eventually→ : ∀ {X n} {P : X → Set}
                         → {t : ∞NWFTree X} {rt : R.Tree X n} {Δ : R.Scope X n}
                         → t ~ R.unfold Δ rt
                         → NWF.Eventually P t
                         → R.Eventually P Δ rt

bisim-unfold-eventually→ : ∀ {X n} {P : X → Set}
                        → {t : NWFTree X} {rt : R.Tree X n} {Δ : R.Scope X n}
                        → NWF.Pointwise _≡_ t (R.tree Δ rt)
                        → NWF.Eventually-step P t
                        → R.Eventually P Δ rt

∞bisim-unfold-eventually→ {X} {n} {P} {t} {rt} {Δ} rs (here px) = R.here Δ rt px (rs .head)
∞bisim-unfold-eventually→ rs (there pt) = bisim-unfold-eventually→ (rs .tree) pt

bisim-unfold-eventually→ {rt = R.loop x} rs pt = R.loop {!bisim-unfold-eventually→ !}
bisim-unfold-eventually→ {rt = R.leaf x} leaf ()
bisim-unfold-eventually→ {rt = R.node1 op x rt} (node1 rs) (node1 pt) = R.there1 (∞bisim-unfold-eventually→ rs pt)
bisim-unfold-eventually→ {rt = R.node2 op x rtl rtr} (node2 rsl rsr) (node2l pt) = R.there2l (∞bisim-unfold-eventually→ rsl pt)
bisim-unfold-eventually→ {rt = R.node2 op x rtl rtr} (node2 rsl rsr) (node2r pt) = R.there2r (∞bisim-unfold-eventually→ rsr pt)
bisim-unfold-eventually→ {rt = R.nodeη op x rt} (nodeη rs) (nodeη pt) = R.thereη (∞bisim-unfold-eventually→ rs pt)


{-
-- Rational to NWF
∞bisim-unfold-eventually← : ∀ {X n} {P : X → Set}
                         → {t : ∞NWFTree X} {rt : R.Tree X n} {Δ : R.Scope X n}
                         → t ~ R.unfold Δ rt
                         → R.Eventually P Δ rt
                         → NWF.Eventually P t

bisim-unfold-eventually← : ∀ {X n} {P : X → Set}
                         → {t : NWFTree X} {rt : R.Tree X n} {Δ : R.Scope X n}
                        → NWF.Pointwise _≡_ t (R.tree Δ rt)
                        → R.Eventually P Δ rt
                        → NWF.Eventually-step P t

∞bisim-unfold-eventually← {P = P} rs (R.loop pt) = {!!}
∞bisim-unfold-eventually← {P = P} rs (R.leaf x) = here (subst P (sym $ rs. head) x)
∞bisim-unfold-eventually← {P = P} rs (R.here1 x) = here (subst P (sym $ rs .head) x)
∞bisim-unfold-eventually← {P = P} rs p@(R.there1 _) = there (bisim-unfold-eventually← (rs .tree) p)
∞bisim-unfold-eventually← {P = P} rs (R.here2 x) = here (subst P (sym $ rs .head) x)
∞bisim-unfold-eventually← {P = P} rs p@(R.there2l _) = there (bisim-unfold-eventually← (rs .tree) p)
∞bisim-unfold-eventually← {P = P} rs p@(R.there2r _) = there (bisim-unfold-eventually← (rs .tree) p)
∞bisim-unfold-eventually← {P = P} rs (R.hereη x) = here (subst P (sym $ rs .head) x)
∞bisim-unfold-eventually← {P = P} rs p@(R.thereη _) = there (bisim-unfold-eventually← (rs .tree) p)

bisim-unfold-eventually← rs (R.loop pt) = {!!}
bisim-unfold-eventually← leaf (R.leaf x) = {!!}
bisim-unfold-eventually← (node1 x₁) (R.here1 x) = {!!}
bisim-unfold-eventually← (node1 x) (R.there1 pt) = {!!}
bisim-unfold-eventually← (node2 x₁ x₂) (R.here2 x) = {!!}
bisim-unfold-eventually← (node2 x x₁) (R.there2l pt) = {!!}
bisim-unfold-eventually← (node2 x x₁) (R.there2r pt) = {!!}
bisim-unfold-eventually← (nodeη x₁) (R.hereη x) = {!!}
bisim-unfold-eventually← (nodeη x) (R.thereη pt) = {!!}

-}
