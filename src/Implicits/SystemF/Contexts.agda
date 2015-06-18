module Implicits.SystemF.Contexts where

open import Prelude
open import Implicits.SystemF.Types

Ctx : ℕ → ℕ → Set
Ctx ν n = Vec (Type ν) n
