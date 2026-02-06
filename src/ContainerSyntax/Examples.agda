
module ContainerSyntax.Examples where

open import Data.Nat
open import Data.Fin

open import ContainerSyntax.Type
open import ContainerSyntax.Term

`List` : Ty 1
`List` = `μ` `1` `+` ((`var` (suc zero)) `×` (`var` zero))


`[]` : ∀ {Γ} → Tm Γ `List`
`[]` = `sup` (`injL` `tt`)

`[_]` : ∀ {X : Ty 0} → Tm [] X → Tm ([] -, X) `List`
`[ x ]` = `sup` (`injR` (`v` x `,` `v` `[]`))

_`-,`_ : ∀ {X : Ty 0} → Tm [] X → Tm ([] -, X) `List` → Tm ([] -, X) `List`
x `-,` xs = `sup` (`injR` ((`v` x) `,` (`v` xs)))
