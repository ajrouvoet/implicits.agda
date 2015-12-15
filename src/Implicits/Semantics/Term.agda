open import Prelude

module Implicits.Semantics.Term
  (TC : Set)
  (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Implicits.Syntax TC _tc≟_
open import SystemF TC as F using ()

⟦_⟧term→ : ∀ {ν} {Δ : ICtx ν} {r} → Δ ⊢ᵣ r → F.Term ν (List.length Δ)
⟦_⟧term→ {ν} {Δ} (r-tabs x) = F.Λ p
  where
    p : F.Term (suc ν) (List.length Δ)
    p = subst (λ u → F.Term (suc ν) u) (length-map _ Δ) ⟦ x ⟧term→
⟦ r-tapp a x ⟧term→ = ⟦ x ⟧term→ F.[ ⟦ a ⟧tp→ ]
⟦ r-ivar x ⟧term→ = F.var (index x)
  where open import Data.List.Any
⟦ r-iabs {a = a} x ⟧term→ = F.λ' ⟦ a ⟧tp→ ⟦ x ⟧term→
⟦ r-iapp f e ⟧term→ = ⟦ f ⟧term→ F.· ⟦ e ⟧term→
