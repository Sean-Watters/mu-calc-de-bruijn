{-# OPTIONS --safe --guardedness #-}
module Rational.Tree.Properties where

open import Relation.Binary.PropositionalEquality

open import MuCalc.Base using (Op₁; Op₂; Opη)
open import Codata.NWFTree as T
open import Rational.Tree as R using ()


bisim-unfold-any∞ : ∀ {X n} {P : X → Set}
                  → {t : ∞NWFTree X} {rt : R.Tree X n} {Δ : R.Scope X n} {{rtnv : R.NonVar rt}}
                  → t ~ R.unfold Δ rt
                  → T.Eventually P t
                  → R.Any P rt

bisim-unfold-any : ∀ {X n} {P : X → Set}
                 → {t : NWFTree X} {rt : R.Tree X n} {Δ : R.Scope X n} {{rtnv : R.NonVar rt}}
                 → T.Pointwise _≡_ t (R.tree Δ rt)
                 → T.Eventually-step P t
                 → R.Any P rt

bisim-unfold-any∞ {rt = rt} {Δ = Δ} rs (here px) = R.here-any Δ rt px (rs .head)
bisim-unfold-any∞ rs (there pt) = bisim-unfold-any (rs .tree) pt 

bisim-unfold-any {rt = R.loop x} rs pt = {!!}
bisim-unfold-any {rt = R.leaf x} leaf ()
bisim-unfold-any {rt = R.node1 op x rt} (node1 rs) (node1 pt) = R.there1 (bisim-unfold-any∞ {{{!!}}} rs pt)
bisim-unfold-any {rt = R.node2 op x rtl rtr} (node2 rsl rsr) (node2l pt) = R.there2l {!!}
bisim-unfold-any {rt = R.node2 op x rtl rtr} (node2 rsl rsr) (node2r pt) = R.there2r {!!}
bisim-unfold-any {rt = R.nodeη op x rt} (nodeη rs) (nodeη pt) = R.thereη {!!}

bisim-unfold-eventually∞ : ∀ {X n} {P : X → Set}
                         → {t : ∞NWFTree X} {rt : R.Tree X n} {Δ : R.Scope X n}
                         → t ~ R.unfold Δ rt
                         → T.Eventually P t
                         → R.Eventually P Δ rt

bisim-unfold-eventually : ∀ {X n} {P : X → Set}
                        → {t : NWFTree X} {rt : R.Tree X n} {Δ : R.Scope X n}
                        → T.Pointwise _≡_ t (R.tree Δ rt)
                        → T.Eventually-step P t
                        → R.Eventually P Δ rt

bisim-unfold-eventually∞ {X} {n} {P} {t} {rt} {Δ} rs (here px) = R.here Δ rt px (rs .head)
bisim-unfold-eventually∞ rs (there pt) = bisim-unfold-eventually (rs .tree) pt

bisim-unfold-eventually {rt = R.loop x} rs pxs = R.loop {!bisim-unfold-any !}
bisim-unfold-eventually {rt = R.leaf x} leaf ()
bisim-unfold-eventually {rt = R.node1 op x rt} (node1 rs) (node1 pt) = R.there1 (bisim-unfold-eventually∞ rs pt)
bisim-unfold-eventually {rt = R.node2 op x rtl rtr} (node2 rsl rsr) (node2l pt) = R.there2l (bisim-unfold-eventually∞ rsl pt)
bisim-unfold-eventually {rt = R.node2 op x rtl rtr} (node2 rsl rsr) (node2r pt) = R.there2r (bisim-unfold-eventually∞ rsr pt)
bisim-unfold-eventually {rt = R.nodeη op x rt} (nodeη rs) (nodeη pt) = R.thereη (bisim-unfold-eventually∞ rs pt)
