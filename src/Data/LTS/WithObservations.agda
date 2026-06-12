
module Data.LTS.WithObservations where

open import Data.LTS.Core

-- LTS with observations
record LTSO : Set₁ where
  field
    lts : LTS
  open LTS lts
  field
    X : Set
    Observe : State -> X
