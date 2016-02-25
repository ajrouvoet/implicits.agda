open import Prelude

module Implicits.Resolution.Ambiguous.Resolution where

open import Data.Fin.Substitution
open import Implicits.Syntax
open import Implicits.Substitutions

data _⊢ᵣ_ {ν} (Δ : ICtx ν) : Type ν → Set where
  r-tabs : ∀ {r} → ictx-weaken Δ ⊢ᵣ r → Δ ⊢ᵣ ∀' r
  r-tapp : ∀ {r} a → Δ ⊢ᵣ ∀' r → Δ ⊢ᵣ (r tp[/tp a ])
  r-ivar : ∀ {r} → r List.∈ Δ → Δ ⊢ᵣ r
  r-iabs : ∀ {a b} → (a List.∷ Δ) ⊢ᵣ b → Δ ⊢ᵣ (a ⇒ b)
  r-iapp : ∀ {a b} → Δ ⊢ᵣ (a ⇒ b) → Δ ⊢ᵣ a → Δ ⊢ᵣ b
