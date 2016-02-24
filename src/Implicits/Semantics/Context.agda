open import Prelude

module Implicits.Semantics.Context where

open import Implicits.Syntax
open import Implicits.Semantics.Type
open import SystemF as F using ()

⟦_⟧ctx→ : ∀ {ν n} → Ktx ν n → F.Ctx ν n
⟦ Γ , Δ ⟧ctx→ = map ⟦_⟧tp→ Γ

