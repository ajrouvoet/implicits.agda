open import Prelude

module Implicits.Semantics.Type
  (TC : Set)
  (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Implicits.Syntax TC _tc≟_
open import SystemF TC as F using ()

⟦_⟧tp→ : ∀ {ν} → Type ν → F.Type ν
⟦ simpl (tc x) ⟧tp→ = F.tc x
⟦ simpl (tvar n) ⟧tp→ = F.tvar n
⟦ simpl (a →' b) ⟧tp→ = ⟦ a ⟧tp→ F.→' ⟦ b ⟧tp→
⟦ a ⇒ b ⟧tp→ = ⟦ a ⟧tp→ F.→' ⟦ b ⟧tp→
⟦ ∀' x ⟧tp→ = F.∀' ⟦ x ⟧tp→

⟦_⟧tps→ : ∀ {ν n} → Vec (Type ν) n → Vec (F.Type ν) n
⟦ v ⟧tps→ = map (⟦_⟧tp→) v
