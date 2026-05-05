module Data.MGraph where

-- Multigraphs are coalgebras of the multiset functor

-- Bags with decidable membership can extensionally look like this, but you need funext
-- in order to get extensional equality of bags this way. See also fresh lists.
Bag : Set → Set
Bag X = X → ℕ

-- Multigraphs type theoretically are the exact same as graphs, except we stop pretending that Set is Prop
record MKripke (At : Set) : Set₁ where
  field
    S : Set
    _~>_ : S → S → Set
    V : At → S → Set
open MKripke

-- We like to think of `S → Set` as powerset, but that should really be `S → Prop`.
-- `S → Set` is more like multisets, but where multiplicity can be an arbirary cardinal (or ordinal?)
-- Let's have some fun with this!
