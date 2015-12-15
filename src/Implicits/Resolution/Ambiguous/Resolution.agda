open import Prelude

module Implicits.Resolution.Ambiguous.Resolution (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Data.Fin.Substitution
open import Implicits.Syntax TC _tc≟_
open import Implicits.Substitutions TC _tc≟_

data _⊢ᵣ_ {ν} (Δ : ICtx ν) : Type ν → Set where
  r-tabs : ∀ {r} → ictx-weaken Δ ⊢ᵣ r → Δ ⊢ᵣ ∀' r
  r-tapp : ∀ {r} a → Δ ⊢ᵣ ∀' r → Δ ⊢ᵣ (r tp[/tp a ])
  r-ivar : ∀ {r} → r List.∈ Δ → Δ ⊢ᵣ r
  r-iabs : ∀ {a b} → (a List.∷ Δ) ⊢ᵣ b → Δ ⊢ᵣ (a ⇒ b)
  r-iapp : ∀ {a b} → Δ ⊢ᵣ (a ⇒ b) → Δ ⊢ᵣ a → Δ ⊢ᵣ b
