
module ContainerSyntax.Examples where

open import Data.Nat
open import Data.Fin

open import ContainerSyntax.Base
open import ContainerSyntax.Term

`List` : Ty 1
`List` = `μ` `1` `+` ((`var` (suc zero)) `×` (`var` zero))


`[]` : Tm `List`
`[]` = `sup` (`injL` `tt`)

`[x]` : Tm `List`
`[x]` = `sup` (`injR` ({!!} `,` {!!}))
