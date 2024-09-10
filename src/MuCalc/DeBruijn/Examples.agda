module MuCalc.DeBruijn.Examples where

open import MuCalc.DeBruijn.Base
open import MuCalc.DeBruijn.Latex
open import MuCalc.DeBruijn.Syntax.Closure
open import Data.Nat
open import Data.Fin
open import Data.String using (String)
open import Data.Unit renaming (⊤ to One)
open import Data.List
open import Function

At = ℕ

ex1 : μML At 0
ex1 = μ (lit 0 ∨ ◆ (var zero))

ex2 : μML At 0
ex2 = ν (μ (◆ (var zero) ∨ (lit 0 ∧ ◆ (var (suc zero)))))

ex2' : μMLε ([] -, ex2)
ex2' = μ' (◆ (var zero) ∨ (lit 0 ∧ ◆ (var (suc zero)))) (recompute-scope-eq _ _)

output : List String
output = (toTeX $ forget-scope ex2')
       ∷ (toTeX $ expandε ex2')
       ∷ []


----------
--- IO ---
----------

postulate
  IO : Set → Set
  printLns : List String → IO One

{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import qualified Data.Text.IO as T #-}
{-# FOREIGN GHC import Data.List #-}
{-# BUILTIN IO IO #-}
{-# COMPILE GHC IO = type IO #-}
{-# COMPILE GHC printLns = \ xs -> mapM_ (T.putStrLn) (intersperse mempty xs)  #-}

{-# NON_TERMINATING #-}
main : IO One
main = printLns output
