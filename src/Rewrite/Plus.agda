{-# OPTIONS --rewriting #-}
module Rewrite.Plus where

open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE +-identityʳ +-suc #-}
