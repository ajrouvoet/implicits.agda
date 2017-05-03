module Implicits.Resolution.Embedding where

open import Prelude

open import Data.Vec
open import Data.List as List hiding (map)

open import Implicits.Syntax
open import SystemF.Everything as F using ()

⟦_⟧tp← : ∀ {ν} → F.Type ν → Type ν
⟦ F.tc x ⟧tp← = simpl (tc x)
⟦ F.tvar n ⟧tp← = simpl (tvar n)
⟦ a F.→' b ⟧tp← = (⟦ a ⟧tp← ⇒ ⟦ b ⟧tp←)
⟦ a F.⟶ b ⟧tp← = simpl (⟦ a ⟧tp← →' ⟦ b ⟧tp←)
⟦ F.∀' x ⟧tp← = ∀' ⟦ x ⟧tp←

⟦_⟧tps← : ∀ {ν n} → Vec (F.Type ν) n → Vec (Type ν) n
⟦ v ⟧tps← = map (⟦_⟧tp←) v

⟦_⟧ctx← : ∀ {ν n} → Vec (F.Type ν) n → List (Type ν)
⟦ v ⟧ctx← = toList $ map ⟦_⟧tp← v

⟦_⟧tp→ : ∀ {ν} → Type ν → F.Type ν
⟦ simpl (tc x) ⟧tp→ = F.tc x
⟦ simpl (tvar n) ⟧tp→ = F.tvar n
⟦ simpl (a →' b) ⟧tp→ = ⟦ a ⟧tp→ F.⟶ ⟦ b ⟧tp→
⟦ a ⇒ b ⟧tp→ = ⟦ a ⟧tp→ F.→' ⟦ b ⟧tp→
⟦ ∀' x ⟧tp→ = F.∀' ⟦ x ⟧tp→

⟦_⟧tps→ : ∀ {ν n} → Vec (Type ν) n → Vec (F.Type ν) n
⟦ v ⟧tps→ = map (⟦_⟧tp→) v

⟦_⟧ctx→ : ∀ {ν} → (Δ : ICtx ν) → Vec (F.Type ν) (List.length (List.map ⟦_⟧tp→ Δ))
⟦ Δ ⟧ctx→ = fromList (List.map ⟦_⟧tp→ Δ)
