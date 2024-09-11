
-- A module for (mu-calculus formula)-shaped trees, storing data at both nodes and leaves
module Data.Tree.Backedges where

open import Data.Maybe
open import Data.Nat
open import Data.Fin

-- Trees with (downwards) {1,2}-ary nodes, that store data at nodes and leaves.
-- Leaves and nodes may also optionally have 1 back-edge.
-- The nat index n keeps track of the distance from the root, and is used to ensure the pointers
-- for backedges are well-scoped.
data Tree (X : Set) (n : ℕ) : Set where
  lf : X → Maybe (Fin n) → Tree X n
  n1 : X → Maybe (Fin n) → Tree X (suc n) → Tree X n
  n2 : X → Maybe (Fin n) → Tree X (suc n) → Tree X (suc n) → Tree X n

-- Paths through trees from tip to root (tip at head).
-- Paths are *not* lists of X's, but rather, lists of increasingly larger Tree X's.
-- The reason is so that when he follow a backedge, we immediately have access to the
-- whole subtree at the destination of the backedge.
data Path (X : Set) : ℕ → Set where
  [] : Path X zero
  _-,_ : ∀ {n} → Path X n → Tree X n → Path X (suc n)

-- From now on, we can traverse the tree as much as we like, including the backedges, so long as
-- we keep that path around and update it as we go. But that sort of manual book-keeping at usage
-- sites is a pain, so let's bake it into a new data type instead:


mutual
  data TreeBE {X : Set} {n : ℕ} (Γ : Path X n) : Set where
    lf : X → Maybe (Fin n) → TreeBE Γ
    n1 : (x : X) → (be : Maybe (Fin n))
       → {t : Tree X (suc n)} → (t' : TreeBE (Γ -, n1 x be t)) → t ≈ t'
       → TreeBE Γ
    n2 : (x : X) → (be : Maybe (Fin n))
       → {t s : Tree X (suc n)} → (t' s' : TreeBE (Γ -, n2 x be t s)) → t ≈ t' → s ≈ s'
       → TreeBE Γ

  data _≈_ {X : Set} {n : ℕ} {Γ : Path X n} : Tree X n → TreeBE Γ → Set where
    lf : (x : X) (be : Maybe (Fin n)) → lf x be ≈ lf x be
    n1 : (x : X) (be : Maybe (Fin n))
       → {t : Tree X (suc n)} {t' : TreeBE (Γ -, n1 x be t)}
       → (p : t ≈ t')
       → n1 x be t ≈ n1 x be t' p
    n2 : (x : X) (be : Maybe (Fin n))
       → {t s : Tree X (suc n)} {t' s' : TreeBE (Γ -, n2 x be t s)}
       → (p : t ≈ t') (q : s ≈ s')
       → n2 x be t s ≈ n2 x be t' s' p q
