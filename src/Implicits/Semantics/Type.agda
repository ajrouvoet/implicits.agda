open import Prelude

module Implicits.Semantics.Type where

open import Data.Vec
open import Implicits.Syntax
open import SystemF as F using ()

⟦_⟧tp→ : ∀ {ν} → Type ν → F.Type ν
⟦ simpl (tc n) ⟧tp→ = F.tc n
⟦ simpl (tvar n) ⟧tp→ = F.tvar n
⟦ simpl (a →' b) ⟧tp→ = ⟦ a ⟧tp→ F.→' ⟦ b ⟧tp→
⟦ a ⇒ b ⟧tp→ = ⟦ a ⟧tp→ F.→' ⟦ b ⟧tp→
⟦ ∀' x ⟧tp→ = F.∀' ⟦ x ⟧tp→

⟦_⟧tps→ : ∀ {ν n} → Vec (Type ν) n → Vec (F.Type ν) n
⟦ v ⟧tps→ = map (⟦_⟧tp→) v
