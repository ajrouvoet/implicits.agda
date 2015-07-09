module Implicits.SystemF.Types.Constructors where

open import Prelude
open import Implicits.SystemF.Types
open import Implicits.SystemF.Substitutions.Types

-- church numerals
tnat : Type 0
tnat = ∀' (((tvar zero) →' (tvar zero)) →' (tvar zero) →' (tvar zero))
