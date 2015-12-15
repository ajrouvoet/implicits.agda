module SystemF.Syntax.Context (TC : Set) where

open import Prelude
open import SystemF.Syntax.Type TC

Ctx : ℕ → ℕ → Set
Ctx ν n = Vec (Type ν) n
