module Data.Kripke where

record Kripke (At : Set) : Set₁ where
  field
    S : Set
    _~>_ : S → S → Set
    V : At → S → Set
open Kripke
