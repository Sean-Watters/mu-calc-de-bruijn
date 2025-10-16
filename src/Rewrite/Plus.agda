{-# OPTIONS --rewriting --local-confluence-check #-}
module Rewrite.Plus where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE +-identityʳ +-suc #-}
