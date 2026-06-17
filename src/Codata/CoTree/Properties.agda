{-# OPTIONS --safe --guardedness #-}
module Codata.CoTree.Properties where

open import Level using (0ℓ) renaming (suc to lsuc)
open import Data.Product
open import Data.Empty
open import Function
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Data.LTS.Core as Lts using (LTS) 
open import Data.LTS.WithObservations
open import Codata.CoTree.Core

private variable
  X : Set

open LTSO

-----------------------------
-- The Bisimilarity Setoid --
-----------------------------

mutual
  ~-reflexive : ∀ {xs ys : CoTree X} → xs ≡ ys → xs ~ ys
  head (~-reflexive refl) = refl
  subtree (~-reflexive refl) = ~-reflexive-step refl
  
  ~-reflexive-step : ∀ {xs ys : CoTree-step X} → xs ≡ ys → Pointwise-step _≡_ xs ys
  ~-reflexive-step {xs = leaf} refl = leaf
  ~-reflexive-step {xs = node1 rs} refl = node1 (~-reflexive refl)
  ~-reflexive-step {xs = node2 rsl rsr} refl = node2 (~-reflexive refl) (~-reflexive refl)
  ~-reflexive-step {xs = nodeη rs} refl = nodeη (~-reflexive refl)


~-refl : ∀ {xs : CoTree X} → xs ~ xs
~-refl {xs = xs} = ~-reflexive {xs = xs} refl

~-refl-step : ∀ {xs : CoTree-step X} → Pointwise-step _≡_ xs xs
~-refl-step {xs = xs} = ~-reflexive-step refl

mutual 
  ~-sym : ∀ {xs ys : CoTree X} → xs ~ ys → ys ~ xs
  head (~-sym rs) = sym (head rs)
  subtree (~-sym rs) = ~-sym-step (subtree rs)

  ~-sym-step : ∀ {xs ys : CoTree-step X} → Pointwise-step _≡_ xs ys → Pointwise-step _≡_ ys xs
  ~-sym-step leaf = leaf
  ~-sym-step (node1 x) = node1 (~-sym x)
  ~-sym-step (node2 x y) = node2 (~-sym x) (~-sym y)
  ~-sym-step (nodeη x) = nodeη (~-sym x)

mutual
  ~-trans : ∀ {xs ys zs : CoTree X} → xs ~ ys → ys ~ zs → xs ~ zs
  head (~-trans rsl rsr) = trans (head rsl) (head rsr)
  subtree (~-trans rsl rsr) = ~-trans-step (subtree rsl) (subtree rsr)
  
  ~-trans-step : ∀ {xs ys zs : CoTree-step X} → Pointwise-step _≡_ xs ys → Pointwise-step _≡_ ys zs → Pointwise-step _≡_ xs zs
  ~-trans-step leaf rsr = rsr
  ~-trans-step (node1 x) (node1 y) = node1 (~-trans x y)
  ~-trans-step (node2 xl xr) (node2 yl yr) = node2 (~-trans xl yl) (~-trans xr yr)
  ~-trans-step (nodeη x) (nodeη y) = nodeη (~-trans x y)

~-isEquivalence : IsEquivalence (_~_ {X})
IsEquivalence.refl ~-isEquivalence = ~-refl
IsEquivalence.sym ~-isEquivalence p = ~-sym p
IsEquivalence.trans ~-isEquivalence p q = ~-trans p q

~-Setoid : Set → Setoid 0ℓ 0ℓ
Setoid.Carrier (~-Setoid X) = CoTree X
Setoid._≈_ (~-Setoid X) = _~_
Setoid.isEquivalence (~-Setoid X) = ~-isEquivalence

module bisim-Reasoning X = pw-Reasoning (setoid X)


------------------------------
-- Interpretation as an LTS --
------------------------------

-- The labels will be the node arities.
-- There is no label for leaves, since they don't have successors.
data Arity : Set where
  lf n1 n2ₗ n2ᵣ nη : Arity

-- The labelled transition relation; it picks out the appropriate
-- successor for the label, up to pointwise equality.
data IsSuccessor' {X : Set} : CoTree-step X → Arity → CoTree X → Set where
  node1 : ∀ {s t} → Pointwise-step _≡_ s (node1 t) → IsSuccessor' s n1 t
  node2ₗ : ∀ {s tl tr} → Pointwise-step _≡_ s (node2 tl tr) → IsSuccessor' s n2ₗ tl
  node2ᵣ : ∀ {s tl tr} → Pointwise-step _≡_ s (node2 tl tr) → IsSuccessor' s n2ᵣ tr
  nodeη : ∀ {s t} → Pointwise-step _≡_ s (nodeη t) → IsSuccessor' s nη t


IsSuccessor : {X : Set} → CoTree X → Arity → CoTree X → Set
IsSuccessor s l t = IsSuccessor' (s .subtree) l t
  


-- We can interpret the entire type of cotrees for any X as an LTS.
-- We could have even intepreted the fibration of cotrees bundled with their
-- parameter X, but then we'd have needed to consider equality of heads up to an  
-- isomorphism of the parameter types; this easier notion suffices.
-- 
-- The states are the cotrees themselves, and there is a transition `s -[l]-> t`
-- if t is exactly the successor of s in direction l.
-- The direct obervations correspond exactly to reading the head.
CoTree-LTSO : (X : Set) → LTSO 0ℓ 0ℓ 0ℓ 0ℓ
CoTree-LTSO X .lts .LTS.State = CoTree X
CoTree-LTSO X .lts .LTS.Label = Arity
CoTree-LTSO X .lts .LTS._-[_]->_ = IsSuccessor
CoTree-LTSO X .Data = X
CoTree-LTSO X .Observe = CoTree.head


-- The identity type is a bisimulation of this LTSO
≡-is-bisimulation : ∀ {X} → IsBisimulation (CoTree-LTSO X) _≡_
≡-is-bisimulation .IsBisimulation.lts-bisim refl l .proj₁ p→p' = _ , p→p' , refl
≡-is-bisimulation .IsBisimulation.lts-bisim refl l .proj₂ q→q' = _ , q→q' , refl
≡-is-bisimulation .IsBisimulation.eq-obervations refl = refl

-- The pointwise lifting of equality is a bisimulation of this LTS
~-is-bisimulation' : ∀ {X} → Lts.IsBisimulation (CoTree-LTSO X .lts) _~_
~-is-bisimulation' p~q l .proj₁ (node1 x) = _ , node1 (~-trans-step ((~-sym p~q) .subtree) x) , ~-refl
~-is-bisimulation' p~q l .proj₁ (node2ₗ x) = _ , node2ₗ (~-trans-step ((~-sym p~q) .subtree) x) , ~-refl
~-is-bisimulation' p~q l .proj₁ (node2ᵣ x) = _ , node2ᵣ (~-trans-step ((~-sym p~q) .subtree) x) , ~-refl
~-is-bisimulation' p~q l .proj₁ (nodeη x) = _ , nodeη (~-trans-step ((~-sym p~q) .subtree) x) , ~-refl
~-is-bisimulation' p~q l .proj₂ (node1 x) = _ , node1 (~-trans-step (p~q .subtree) x) , ~-refl
~-is-bisimulation' p~q l .proj₂ (node2ₗ x) =  _ , node2ₗ (~-trans-step (p~q .subtree) x) , ~-refl
~-is-bisimulation' p~q l .proj₂ (node2ᵣ x) = _ , node2ᵣ (~-trans-step (p~q .subtree) x) , ~-refl
~-is-bisimulation' p~q l .proj₂ (nodeη x) = _ , nodeη (~-trans-step (p~q .subtree) x) , ~-refl

~-is-bisimulation : ∀ {X} → IsBisimulation (CoTree-LTSO X) _~_
~-is-bisimulation .IsBisimulation.lts-bisim = ~-is-bisimulation' 
~-is-bisimulation .IsBisimulation.eq-obervations p~q = p~q .head


----------------------------------------
-- A Different Notion of Bisimilarity --
----------------------------------------

-- Bisimilarity for LTS(O)'s makes it hard to infer that bisimilar trees have root nodes with the same arity.
-- We introduce a more concrete notion of bisimulation specialised to cotrees, which makes this explicit, and
-- show that it implies the usual notion of bisimulation. (TODO: does it even coincide?)

data SameArity' {X : Set} : CoTree-step X → CoTree-step X → Set where
  leaf : SameArity' leaf leaf
  node1 : ∀ s t → SameArity' (node1 s) (node1 t)
  node2 : ∀ sl sr tl tr → SameArity' (node2 sl sr) (node2 tl tr)
  nodeη : ∀ s t → SameArity' (nodeη s) (nodeη t)

SameArity : {X : Set} → CoTree X → CoTree X → Set
SameArity s t = SameArity' (s .subtree) (t .subtree)

SameArity-refl : ∀ {X s} → SameArity {X} s s
SameArity-refl {s = s} with (s .subtree)
... | leaf = leaf
... | node1 x = node1 x x
... | node2 l r = node2 l r l r
... | nodeη x = nodeη x x

data IsLeaf {X : Set} : CoTree-step X → Set where
  leaf : IsLeaf leaf

IsLeaf-fromEq : {x : CoTree-step X} → x ≡ leaf → IsLeaf x
IsLeaf-fromEq refl = leaf

IsLeaf-SameArity : {x : CoTree-step X} → IsLeaf x → SameArity' leaf x
IsLeaf-SameArity leaf = leaf

data IsUnary {X : Set} : CoTree-step X → Set where
  node1 : ∀ s → IsUnary (node1 s)

IsUnary-prop : ∀ {X} {s : CoTree-step X} → (p q : IsUnary s) → p ≡ q
IsUnary-prop (node1 s) (node1 .s) = refl

IsUnary-fromEq : {x : CoTree-step X} {s : CoTree X} → x ≡ node1 s → IsUnary x
IsUnary-fromEq refl = node1 _

IsUnary-SameArity : {x : CoTree-step X} {s : CoTree X} → IsUnary x → SameArity' (node1 s) x
IsUnary-SameArity (node1 _) = node1 _ _

succ : ∀ {X} {s : CoTree-step X} → IsUnary s → CoTree X
succ {s = node1 t} _ = t

data IsBinary {X : Set} : CoTree-step X → Set where
  node2 : ∀ l r → IsBinary (node2 l r)

IsBinary-prop : ∀ {X} {s : CoTree-step X} → (p q : IsBinary s) → p ≡ q
IsBinary-prop (node2 l r) (node2 .l .r) = refl

IsBinary-fromEq : {x : CoTree-step X} {l r : CoTree X} → x ≡ node2 l r → IsBinary x
IsBinary-fromEq refl = node2 _ _

IsBinary-SameArity : {x : CoTree-step X} {l r : CoTree X} → IsBinary x → SameArity' (node2 l r) x
IsBinary-SameArity (node2 _ _) = node2 _ _ _ _

succl : ∀ {X} {s : CoTree-step X} → IsBinary s → CoTree X
succl {s = node2 l r} _ = l

succr : ∀ {X} {s : CoTree-step X} → IsBinary s → CoTree X
succr {s = node2 l r} _ = r

data IsBinder {X : Set} : CoTree-step X → Set where
  nodeη : ∀ s → IsBinder (nodeη s)

IsBinder-prop : ∀ {X} {s : CoTree-step X} → (p q : IsBinder s) → p ≡ q
IsBinder-prop (nodeη s) (nodeη .s) = refl

IsBinder-fromEq : {x : CoTree-step X} {s : CoTree X} → x ≡ nodeη s → IsBinder x
IsBinder-fromEq refl = nodeη _

IsBinder-SameArity : {x : CoTree-step X} {s : CoTree X} → IsBinder x → SameArity' (nodeη s) x
IsBinder-SameArity (nodeη _) = nodeη _ _

succη : ∀ {X} {s : CoTree-step X} → IsBinder s → CoTree X
succη {s = nodeη t} _ = t

record IsCotreeBisimulation {X : Set} (R : CoTree X → CoTree X → Set) : Set where
  field
    same-arity : ∀ {s t} → R s t → SameArity s t

    nullary : ∀ {s t} → R s t
            → IsLeaf (s .subtree) → IsLeaf (t .subtree)
            → (s .head ≡ t .head)

    unary   : ∀ {s t} → R s t
            → (s' : IsUnary (s .subtree)) → (t' : IsUnary (t .subtree))
            → (s .head ≡ t .head) × (R (succ s') (succ t'))

    binary  : ∀ {s t} → R s t
            → (s' : IsBinary (s .subtree)) (t' : IsBinary (t .subtree))
            → (s .head ≡ t .head) × (R (succl s') (succl t'))
            × (R (succr s') (succr t'))

    binder  : ∀ {s t} → R s t
            → (s' : IsBinder (s .subtree)) → (t' : IsBinder (t .subtree))
            → (s .head ≡ t .head) × (R (succη s') (succη t'))

open IsCotreeBisimulation

succ-subst : ∀ {X} ({s} t : CoTree X) (eq : node1 s ≡ t .subtree) → succ {X} {t .subtree} (subst IsUnary {node1 s} {t .subtree} eq (node1 s)) ≡ s
succ-subst t eq with t .subtree
succ-subst t refl | z = refl

succl-subst : ∀ {X} ({sl sr} t : CoTree X) (eq : node2 sl sr ≡ t .subtree) → succl (subst IsBinary eq (node2 sl sr)) ≡ sl
succl-subst t eq with t .subtree
succl-subst t refl | z = refl

succr-subst : ∀ {X} ({sl sr} t : CoTree X) (eq : node2 sl sr ≡ t .subtree) → succr (subst IsBinary eq (node2 sl sr)) ≡ sr
succr-subst t eq with t .subtree
succr-subst t refl | z = refl

succη-subst : ∀ {X} ({s} t : CoTree X) (eq : nodeη s ≡ t .subtree) → succη (subst IsBinder eq (nodeη s)) ≡ s
succη-subst t eq with t .subtree
succη-subst t refl | z = refl

-- Pointwise equality is the greatest cotree bisimulation; this would have been
-- hard to prove directly for LTS bisimulations
~-greatest-cotree-bisimulation : ∀ {X} {R : CoTree X → CoTree X → Set}
                        → IsCotreeBisimulation R
                        → (∀ {s t : CoTree X} → R s t → s ~ t)
~-greatest-cotree-bisimulation {R = R} bisim {s'} {t'} Rst .head
  with s' .subtree in eq | t' .subtree in eq2 | (bisim .same-arity) Rst
... | _ | _ | leaf
  = (bisim .nullary) Rst (subst IsLeaf (sym eq) leaf) (subst IsLeaf (sym eq2) leaf)
... | _ | _ | node1 s t
  = let (p , ps) = (bisim .unary) Rst (subst IsUnary (sym eq) (node1 s))
                                      (subst IsUnary (sym eq2) (node1 t))
    in p
... | _ | _ | node2 sl sr tl tr
  = let (p , psl , psr) = (bisim .binary) Rst (subst IsBinary (sym eq) (node2 sl sr))
                                              (subst IsBinary (sym eq2) (node2 tl tr))
    in p
... | _ | _ | nodeη s t
  = let (p , ps) = (bisim .binder) Rst (subst IsBinder (sym eq) (nodeη s))
                                       (subst IsBinder (sym eq2) (nodeη t))
    in p

~-greatest-cotree-bisimulation {R = R} bisim {s'} {t'} Rst .subtree
  with s' .subtree in eq | t' .subtree in eq2 | (bisim .same-arity) Rst
... | _ | _ | leaf
  = leaf
... | _ | _ | node1 s t
  = let (p , ps) = (bisim .unary) Rst (subst IsUnary (sym eq) (node1 s))
                                      (subst IsUnary (sym eq2) (node1 t))
    in node1 (~-greatest-cotree-bisimulation bisim (subst₂ R (succ-subst s' (sym eq) )
                                                      (succ-subst t' (sym eq2))
                                                      ps))
... | _ | _ | node2 sl sr tl tr
  = let (p , psl , psr) = (bisim .binary) Rst (subst IsBinary (sym eq) (node2 sl sr))
                                              (subst IsBinary (sym eq2) (node2 tl tr))
    in node2 (~-greatest-cotree-bisimulation bisim (subst₂ R (succl-subst s' (sym eq))
                                                      (succl-subst t' (sym eq2))
                                                      psl))
             (~-greatest-cotree-bisimulation bisim (subst₂ R (succr-subst s' (sym eq))
                                                      (succr-subst t' (sym eq2))
                                                      psr))
... | _ | _ | nodeη s t
  = let (p , ps) = (bisim .binder) Rst (subst IsBinder (sym eq) (nodeη s))
                                       (subst IsBinder (sym eq2) (nodeη t))
    in nodeη (~-greatest-cotree-bisimulation bisim (subst₂ R (succη-subst s' (sym eq))
                                                      (succη-subst t' (sym eq2))
                                                      ps))

--------------------------------------------------------------
-- The two notions of bisimulation coincide
--------------------------------------------------------------

-- To show that the two notions of bisimulation coincide, we must first show that two trees
-- being bisimilar (in the sense of the LTS) implies that they have the same arity. This is
-- intuitively easy, but in practice it's pretty gnarly and technical.

-- The intuition is that we have a 1:1 relationship between the labels of the outgoing transitions
-- and the arities of the nodes at their source. And that's it; that's the whole proof. Showing this
-- formally just requires a massive comparison of cases. The lack of eta equality for coinductive records
-- gets in the way a bit as well.

-- We first need to explicitly spell out the restrictions that the IsSuccessor relation places
-- on the shape of the predecessor. ie, leaf has no successors, node1 has only n1-labelled sucessors,
-- etc

leaf-no-successors : ∀ {l} {s : CoTree-step X} {t : CoTree X} → s ≡ leaf → ¬ (IsSuccessor' s l t)
leaf-no-successors refl (node1 ())
leaf-no-successors refl (node2ₗ ())
leaf-no-successors refl (node2ᵣ ())
leaf-no-successors refl (nodeη ())

unary-only-n1 : ∀ {l} {s : CoTree-step X} {t : CoTree X} → IsUnary s → ¬ (l ≡ n1) → ¬ (IsSuccessor' s l t)
unary-only-n1 (node1 _) l≠n1 (node1 _) = l≠n1 refl

-- Because there are two binary cases, it is slightly easier to say what they are not rather than what they are
binary-not-n1 : ∀ {l} {s : CoTree-step X} {t : CoTree X} → IsBinary s → l ≡ n1 → ¬ (IsSuccessor' s l t)
binary-not-n1 (node2 _ _) refl (node1 ())

binary-not-nη : ∀ {l} {s : CoTree-step X} {t : CoTree X} → IsBinary s → l ≡ nη → ¬ (IsSuccessor' s l t)
binary-not-nη (node2 _ _) refl (nodeη ())

binder-only-nη : ∀ {l} {s : CoTree-step X} {t : CoTree X} → IsBinder s → ¬ (l ≡ nη) → ¬ (IsSuccessor' s l t)
binder-only-nη (nodeη _) l≠nη (nodeη _) = l≠nη refl

-- Now we prove that two trees being bisimilar implies they have the same arity. This requires
-- handling all 25 cases, using the above to discharge the impossible ones.

Bisim⇒SameArity-leaf : ∀ {X} {R : CoTree X → CoTree X → Set}
                     → Lts.IsBisimulation (CoTree-LTSO X .lts) R
                     → ∀ {s} → IsLeaf (s .subtree) → ∀ {t}
                     → R s t
                     → IsLeaf (t .subtree)
Bisim⇒SameArity-leaf bisim {s} leaf-s {t} Rst with s .subtree in eqS | t .subtree in eqT
Bisim⇒SameArity-leaf bisim leaf Rst | .leaf | leaf = leaf
Bisim⇒SameArity-leaf bisim leaf Rst | .leaf | node1 t'
  with bisim Rst n1 .proj₂ (node1 (~-reflexive-step eqT)) 
... | p , lf→p , Rpt = ⊥-elim (leaf-no-successors eqS lf→p)
Bisim⇒SameArity-leaf bisim leaf Rst | .leaf | node2 tl tr 
  with bisim Rst n2ₗ .proj₂ (node2ₗ (~-reflexive-step eqT)) 
... | p , lf→p , Rpt = ⊥-elim (leaf-no-successors eqS lf→p)
Bisim⇒SameArity-leaf bisim leaf Rst | .leaf | nodeη t' 
  with bisim Rst nη .proj₂ (nodeη (~-reflexive-step eqT)) 
... | p , lf→p , Rpt = ⊥-elim (leaf-no-successors eqS lf→p)

Bisim⇒SameArity-node1 : ∀ {X} {R : CoTree X → CoTree X → Set}
                      → Lts.IsBisimulation (CoTree-LTSO X .lts) R
                      → ∀ {s} → IsUnary (s .subtree) → ∀ {t}
                      → R s t
                      → IsUnary (t .subtree)
Bisim⇒SameArity-node1 bisim {s} node1-s {t} Rst with s .subtree in eqS | t .subtree in eqT
Bisim⇒SameArity-node1 bisim {s} (node1 s') {t} Rst | ._ | leaf
  with bisim Rst n1 .proj₁ {s'} (node1 (~-reflexive-step eqS))
... | p , t→p , Rs'p = ⊥-elim (leaf-no-successors eqT t→p)
Bisim⇒SameArity-node1 bisim {s} (node1 s') Rst | ._ | node1 t' = node1 t'
Bisim⇒SameArity-node1 bisim {s} (node1 s') Rst | ._ | node2 tl tr 
  with bisim Rst n2ₗ .proj₂ {tl} (node2ₗ (~-reflexive-step eqT))
... | p , t→p , Rs'p = ⊥-elim (unary-only-n1 {s = s .subtree} (IsUnary-fromEq eqS) (λ ()) t→p)
Bisim⇒SameArity-node1 bisim {s} (node1 s') Rst | ._ | nodeη t'
  with bisim Rst nη .proj₂ {t'} (nodeη (~-reflexive-step eqT))
... | p , t→p , Rs'p = ⊥-elim (unary-only-n1 {s = s .subtree} (IsUnary-fromEq eqS) (λ ()) t→p)

Bisim⇒SameArity-node2 : ∀ {X} {R : CoTree X → CoTree X → Set}
                      → Lts.IsBisimulation (CoTree-LTSO X .lts) R
                      → ∀ {s} → IsBinary (s .subtree) → ∀ {t}
                      → R s t
                      → IsBinary (t .subtree)
Bisim⇒SameArity-node2 bisim {s} node2-s {t} Rst with s .subtree in eqS | t .subtree in eqT
Bisim⇒SameArity-node2 bisim {s} (node2 sl sr) {t} Rst | ._ | leaf 
  with bisim Rst n2ₗ .proj₁ {sl} (node2ₗ (~-reflexive-step eqS))
... | p , t→p , Rs'p = ⊥-elim (leaf-no-successors eqT t→p)
Bisim⇒SameArity-node2 bisim {s} (node2 sl sr) {t} Rst | ._ | node1 t' 
  with bisim Rst n1 .proj₂ {t'} (node1 (~-reflexive-step eqT))
... | p , t→p , Rs'p = ⊥-elim (binary-not-n1 (IsBinary-fromEq eqS) refl t→p)
Bisim⇒SameArity-node2 bisim {s} (node2 sl sr) {t} Rst | ._ | node2 tl tr = node2 tl tr
Bisim⇒SameArity-node2 bisim {s} (node2 sl sr) {t} Rst | ._ | nodeη t' 
  with bisim Rst nη .proj₂ {t'} (nodeη (~-reflexive-step eqT))
... | p , t→p , Rs'p = ⊥-elim (binary-not-nη (IsBinary-fromEq eqS) refl t→p)

Bisim⇒SameArity-nodeη : ∀ {X} {R : CoTree X → CoTree X → Set}
                      → Lts.IsBisimulation (CoTree-LTSO X .lts) R
                      → ∀ {s} → IsBinder (s .subtree) → ∀ {t}
                      → R s t
                      → IsBinder (t .subtree)
Bisim⇒SameArity-nodeη bisim {s} nodeη-s {t} Rst with s .subtree in eqS | t .subtree in eqT
Bisim⇒SameArity-nodeη bisim {s} (nodeη s') {t} Rst | ._ | leaf 
  with bisim Rst nη .proj₁ {s'} (nodeη (~-reflexive-step eqS))
... | p , t→p , Rs'p = ⊥-elim (leaf-no-successors eqT t→p)
Bisim⇒SameArity-nodeη bisim {s} (nodeη s') {t} Rst | ._ | node1 t' 
  with bisim Rst n1 .proj₂ {t'} (node1 (~-reflexive-step eqT))
... | p , t→p , Rs'p = ⊥-elim (binder-only-nη (IsBinder-fromEq eqS) (λ ()) t→p)
Bisim⇒SameArity-nodeη bisim {s} (nodeη s') {t} Rst | ._ | node2 tl tr 
  with bisim Rst n2ₗ .proj₂ {tl} (node2ₗ (~-reflexive-step eqT))
... | p , t→p , Rs'p = ⊥-elim (binder-only-nη (IsBinder-fromEq eqS) (λ ()) t→p)
Bisim⇒SameArity-nodeη bisim {s} (nodeη s') {t} Rst | ._ | nodeη t' = nodeη t'

Bisim⇒SameArity : ∀ {X} {R : CoTree X → CoTree X → Set}
                → Lts.IsBisimulation (CoTree-LTSO X .lts) R
                → ∀ {s t} → R s t → SameArity s t
Bisim⇒SameArity bisim {s} Rst with s .subtree in eq
... | leaf = IsLeaf-SameArity (Bisim⇒SameArity-leaf bisim (IsLeaf-fromEq eq) Rst)
... | node1 _ = IsUnary-SameArity (Bisim⇒SameArity-node1 bisim (IsUnary-fromEq eq) Rst)
... | node2 _ _ = IsBinary-SameArity (Bisim⇒SameArity-node2 bisim (IsBinary-fromEq eq) Rst)
... | nodeη _ = IsBinder-SameArity (Bisim⇒SameArity-nodeη bisim (IsBinder-fromEq eq) Rst)

-- First part done!!!

---------

-- To finish the proof of this first direction, we need to show that if two trees of the same
-- arity are bisimilar, then they have equal heads and bisimilar subtrees. And we have to do
-- this separately for each of the four possible arities.


Bisim⇒CotreeBisim : ∀ {X} {R : CoTree X → CoTree X → Set}
                  → IsBisimulation (CoTree-LTSO X) R
                  → IsCotreeBisimulation R
Bisim⇒CotreeBisim bisim .same-arity = Bisim⇒SameArity (bisim .IsBisimulation.lts-bisim)
Bisim⇒CotreeBisim bisim .nullary {s} {t} Rst u v = {!bisim Rst !}
Bisim⇒CotreeBisim bisim .unary = {!!}
Bisim⇒CotreeBisim bisim .binary = {!!}
Bisim⇒CotreeBisim bisim .binder = {!!}

-- TODO: It would be proper to also assert CotreeBisim⇒Bisim, showing that the two notions are inter-derivable.
-- Ideally these two maps will even be mutually inverse, but I don't really care about that.
CotreeBisim⇒Bisim : ∀ {X} {R : CoTree X → CoTree X → Set}
                  → IsCotreeBisimulation R
                  → IsBisimulation (CoTree-LTSO X) R
CotreeBisim⇒Bisim = {!!}

------------------
-- Bisimilarity --
------------------

-- Pointwise equality is therefore also the greatest bisimulation of the cotrees
-- LTS:
~-greatest-bisimulation : ∀ {X} {R : CoTree X → CoTree X → Set}
                        → IsBisimulation (CoTree-LTSO X) R
                        → (∀ {s t : CoTree X} → R s t → s ~ t)
~-greatest-bisimulation = ~-greatest-cotree-bisimulation ∘ Bisim⇒CotreeBisim

-- And thus, pointwise lifting of equality really is bisimilarity of cotrees.
~-is-bisimilarity : ∀ {X} → IsBisimilarity (CoTree-LTSO X) _~_
~-is-bisimilarity p q .proj₁ p~q = _~_ , ~-is-bisimulation , p~q
~-is-bisimilarity p q .proj₂ (R , R-bisim , Rpq) = ~-greatest-bisimulation R-bisim Rpq

