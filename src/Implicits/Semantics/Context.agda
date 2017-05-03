open import Prelude

module Implicits.Semantics.Context where

open import Implicits.Syntax
open import Implicits.Semantics.Type
open import SystemF as F using ()

open import Data.Vec

⟦_⟧ctx→ : ∀ {ν n} → Ctx ν n → F.Ctx ν n
⟦ Γ ⟧ctx→ = map ⟦_⟧tp→ Γ

