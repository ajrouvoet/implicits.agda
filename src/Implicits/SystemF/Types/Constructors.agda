module Implicits.SystemF.Types.Constructors where

open import Prelude
open import Implicits.SystemF.Types
open import Implicits.SystemF.Substitutions.Types

-- construct an ml style function type
-- induction is well-founded on the remaining number of ∀' constructors
infixl 6 _→ml_
{-# NO_TERMINATION_CHECK #-}
_→ml_ : ∀ {ν} → Type ν → Type ν → Type ν
∀' a   →ml b = ∀' (a →ml (tp-weaken b))
tvar n →ml ∀' b =  ∀' (tp-weaken (tvar n) →ml b)
tvar n →ml tvar y = tvar n →' tvar y
tvar n →ml a →' b = tvar n →' (a →' b)
a →' b →ml ∀' c = ∀' (tp-weaken (a →' b) →ml c)
a →' b →ml tvar n = (a →' b) →' tvar n
a →' b →ml c →' d = (a →' b) →' (c →' d)

-- church numerals
tnat : Type 0
tnat = ∀' (((tvar zero) →' (tvar zero)) →' (tvar zero) →' (tvar zero))

test = (tnat →' tnat) →ml tnat
