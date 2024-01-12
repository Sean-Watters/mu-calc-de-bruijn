{-# OPTIONS -v sean:50 #-}
-- Inspired by Guillaume's work on linear decidable equality,
-- available at: https://github.com/gallais/potpourri/blob/main/agda/poc/LinearDec.agda

module Relation.Binary.Dec where

open import Level renaming (zero to lzero; suc to lsuc)
open import Reflection
open import Reflection.TCM.Instances

open import Data.Bool
open import Data.Empty
open import Data.List as L
open import Data.List.Effectful
open import Data.List.Instances
open import Data.List.Relation.Unary.All using ()
open import Data.Nat
open import Data.Unit
open import Data.Product

open import Function

-- A constructor is "simple" if all of its arguments are either to itself,
-- or another simple constructor


{-
mutual
  isSimpleConstructor : Term → TC Bool
  isSimpleConstructor (con n args) = do
    pure true
  isSimpleConstructor _ = pure false

  areSimpleArgs : List (Arg Term) → TC Bool
  areSimpleArgs [] = pure true
  areSimpleArgs (arg _ tm ∷ args) = do
    tmSimple <- isSimpleConstructor {!!}

-}


open TraversableM {lzero} tcMonad


-- data OrderableConstructor ()

getConstructorArgs : Term → TC (List (Arg Term))
getConstructorArgs (var x args) = typeError (strErr "var" ∷ [])
getConstructorArgs (con c args) = typeError (strErr "con" ∷ [])
getConstructorArgs (def f args) = pure args
getConstructorArgs (lam v t) = typeError (strErr "lam" ∷ [])
getConstructorArgs (pat-lam cs args) = typeError (strErr "pat-lam" ∷ [])
getConstructorArgs (pi (arg _ X) (abs x Y)) = do -- (pi (arg _ X) (abs x Y)) = (x : X) → Y x
  {!!}
getConstructorArgs (agda-sort s) = typeError (strErr "agda-sort" ∷ [])
getConstructorArgs (lit l) = typeError (strErr "lit" ∷ [])
getConstructorArgs (meta x x₁) = typeError (strErr "meta" ∷ [])
getConstructorArgs unknown = typeError (strErr "hole" ∷ [])

getConstructors : Name → TC (List (Name × List (Arg Term)))
getConstructors d = do
  data-type pars cns <- getDefinition d
    where _ → typeError (nameErr d ∷ strErr " is not the name of a data type." ∷ [])
  ts <- mapM getType cns -- the types of each constructor (aka the constructor as a term)
  mapM (λ t → debugPrint "sean" 5 (termErr t ∷ [])) ts
  -- mapM (λ {n , t} → n , (getConstructorArgs t)) (zip cns ts)
  {!!}

genPSTO : Name → TC ⊤
genPSTO d = do
  cs <- getConstructors d
  -- todo add a check that all the constructors are "simple"
  pure tt
  -- debugPrint "sean" 5 (L.map termErr cs)



macro
  test : Term → TC ⊤
  test hole = do
    genPSTO (quote ℕ)
    unify hole {!!}

foo = test

-- If every argument of every constructor an inductive data type is
-- PSTO-able, then the datatype itself is.

-- Macro which generates a diagonal relation.
-- ie, terms are related if they have the same constructors


--
