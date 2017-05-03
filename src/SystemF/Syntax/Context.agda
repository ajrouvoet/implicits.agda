module SystemF.Syntax.Context where

open import Prelude
open import SystemF.Syntax.Type
open import Data.Vec

Ctx : ℕ → ℕ → Set
Ctx ν n = Vec (Type ν) n
