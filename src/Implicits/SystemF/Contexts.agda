module Implicits.SystemF.Contexts (TC : Set) where

open import Prelude
open import Implicits.SystemF.Types TC

Ctx : ℕ → ℕ → Set
Ctx ν n = Vec (Type ν) n
