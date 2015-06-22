module Implicits.SystemF.Types.Constructors where

open import Prelude
open import Implicits.SystemF.Types
open import Implicits.SystemF.Substitutions.Types

-- construct an ml style function type
-- induction is well-founded on the remaining number of ∀' constructors
{-# NO_TERMINATION_CHECK #-}
_→ml_ : ∀ {ν} → Type ν → Type ν → Type ν
(a →' b) →ml ∀' c = ∀' (tp-weaken (a →' b) →ml c)
tvar n →ml ∀' b =  ∀' (tp-weaken (tvar n) →ml b)
∀' a →ml b = ∀' (a →ml (tp-weaken b))
a →ml b = a →' b
