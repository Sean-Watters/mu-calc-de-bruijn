
module MuCalc.Latex where

open import MuCalc.Base
open import Data.String
open import Data.Fin as Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Nat
open import Data.List using (List; []; _∷_)
open import Data.Char as Char
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Function

n-_ : ∀ {n} → Fin n → ℕ
n-_ {suc n} fzero = n
n-_ (fsuc x) = (n- x)

-- Labelling binders in a "path-clean" manner; the result is not clean as different branches
-- may use the same name for different SFs, but also may not be maximally unclean depending on
-- FP dependencies within each path.
-- a, b, c, ... y, z, aa, bb, cc, ... zz, aaa, bbb, ....
-- The n-x makes it count from the root, rather than from the leaves (which just wouldn't work at all).
bvName : ∀ {n} → Fin n → String
bvName x = let y = n- x
           in replicate (suc $ y / 26) (Char.fromℕ $ 65 + (y % 26))

-- Helper functions for reducing unnecessary parentheses:
shouldParen₁ : ∀ {At n} → μML At n → Bool
shouldParen₁ (μML₂ _ _ _) = true -- ◆(ϕ ∧ ψ)
shouldParen₁ (μMLη _ _) = true   -- ◆(μX.ϕ)
shouldParen₁ _ = false           -- ◆■ϕ    ◆p


shouldParen₂ : ∀ {At n} → Op₂ → μML At n → Bool
shouldParen₂ _ (μMLη _ _) = true        -- ϕ ∧ (μX.ϕ)
shouldParen₂ and (μML₂ and _ _) = false -- ϕ ∧ ψ ∧ ξ
shouldParen₂ and (μML₂ or _ _) = true   -- ϕ ∧ (ψ ∨ ξ)
shouldParen₂ or (μML₂ or _ _) = false   -- ϕ ∨ ψ ∨ ξ
shouldParen₂ or (μML₂ and _ _) = true   -- ϕ ∨ (ψ ∧ ξ)
shouldParen₂ _ _ = false                -- ■ϕ ∧ p

maybeParen : Bool → String → String
maybeParen shouldParen s = if shouldParen
                           then "(" ++ s ++ ")"
                           else s

-- in general for any set At
toTeX' : ∀ {At n} → (At → String) → μML At n → String
toTeX' r (var x) = bvName x
toTeX' r ⊤ = "\\top{}"
toTeX' r ⊥ = "\\bot{}"
toTeX' r (lit x) = r x
toTeX' r (¬lit x) = "\\neg{} " ++ r x
toTeX' r (■ ϕ) = "\\Box{} " ++ maybeParen (shouldParen₁ ϕ) (toTeX' r ϕ)
toTeX' r (◆ ϕ) = "\\Diamond{} " ++ maybeParen (shouldParen₁ ϕ) (toTeX' r ϕ)
toTeX' r (ϕ ∧ ψ) = maybeParen (shouldParen₂ and ϕ) (toTeX' r ϕ) ++ " \\land " ++  maybeParen (shouldParen₂ and ψ) (toTeX' r ψ)
toTeX' r (ϕ ∨ ψ) = maybeParen (shouldParen₂ or ϕ) (toTeX' r ϕ) ++ " \\lor " ++  maybeParen (shouldParen₂ or ψ) (toTeX' r ψ)
toTeX' {n = n} r (μ ϕ) = "\\mu{} " ++ (bvName {suc n} fzero) ++ ". " ++ toTeX' r ϕ
toTeX' {n = n} r (ν ϕ) = "\\nu{} " ++ (bvName {suc n} fzero) ++ ". " ++ toTeX' r ϕ

-- In practice, we always have At = ℕ
propName : ℕ → String
propName x = replicate (suc $ x / 26) (Char.fromℕ $ 112 + (x % 26))

toTeX : ∀ {n} → μML ℕ n → String
toTeX = toTeX' propName


----------------------------------------------------
-- Rendering Trees with graphviz
----------------------------------------------------


