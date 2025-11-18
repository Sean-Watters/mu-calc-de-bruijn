module Data.IKripke where

open import Data.Kripke
open import Data.Product
open import Data.Unit

record IKripke (Atom : Set) : Set₁ where
  field
    -- A graph which the Kripke model is indexed over
    Vert : Set
    Edge : Vert → Vert → Set

    -- States of the Kripke model live at vertices
    State : Vert → Set

    -- Transitions can happen between states in the Kripke model
    -- when there is a (directed) edge connecting the vertices that
    -- the states live at
    Transition : ∀ {x y} → Edge x y → State x → State y → Set

    -- Each propositional atom has a valuation at each state
    val : ∀ {v} → Atom → State v → Set
open IKripke

-- We get back a normal kripke model by erasing the graph, then gluing
-- together the families of states and transitions
forget : ∀ {At} → IKripke At → Kripke At
forget M .Kripke.S = Σ[ v ∈ M .Vert ] (M .State v)
(forget M .Kripke._~>_) (v , s) (v' , s') = Σ[ e ∈ M .Edge v v' ] (M .Transition e s s')
forget M .Kripke.V at (v , s) = M .val at s

-- We can freely add a graph with one vertex and a self edge.
-- Todo: Is this actually left-adjoint?
free : ∀ {At} → Kripke At → IKripke At
free M .Vert = ⊤
free M .Edge _ _ = ⊤
free M .State _ = M .Kripke.S
free M .Transition _ = M .Kripke._~>_
free M .val = M .Kripke.V

-- Theres another obvious free graph we could add, which is just
-- the kripke frame itself. Then each vertex/edge has a unique
-- state/transition.
-- Todo: Is this actually right-adjoint?
cofree : ∀ {At} → Kripke At → IKripke At
cofree M .Vert = M .Kripke.S
cofree M .Edge = M .Kripke._~>_
cofree M .State _ = ⊤
cofree M .Transition _ _ _ = ⊤
cofree M .val {s} x _ = M .Kripke.V x s
