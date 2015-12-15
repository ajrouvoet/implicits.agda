open import Prelude

module Implicits.Semantics.Context
  (TC : Set)
  (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Implicits.Syntax TC _tc≟_
open import Implicits.Semantics.Type TC _tc≟_
open import SystemF TC as F using ()

⟦_⟧ctx : ∀ {ν n} → Ktx ν n → F.Ctx ν n
⟦ Γ , Δ ⟧ctx = map ⟦_⟧tp→ Γ

