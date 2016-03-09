module SystemF.Syntax.Context where

open import Prelude
open import SystemF.Syntax.Type

Ctx : ℕ → ℕ → Set
Ctx ν n = Vec (Type ν) n
