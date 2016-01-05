open import Prelude

module Implicits.Resolution.Finite2.Resolution (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Coinduction
open import Data.Fin.Substitution
open import Implicits.Syntax TC _tc≟_
open import Implicits.Substitutions TC _tc≟_
open import Induction
open import Induction.Nat
open import Relation.Binary using (Rel)

mutual

  data _⊢_↓_ {ν} (Δ : ICtx ν) : Type ν → SimpleType ν → Set where
    i-simp : ∀ a → Δ ⊢ simpl a ↓ a
    i-iabs : ∀ {ρ₁ ρ₂ a} → Δ ⊢ᵣ ρ₁ → Δ ⊢ ρ₂ ↓ a → Δ ⊢ ρ₁ ⇒ ρ₂ ↓ a
    i-tabs : ∀ {ρ a} b → Δ ⊢ ρ tp[/tp b ] ↓ a → Δ ⊢ ∀' ρ ↓ a

  data _⊢ᵣ_ {ν} (Δ : ICtx ν) : Type ν → Set where
    r-simp : ∀ {r τ} → r List.∈ Δ → Δ ⊢ r ↓ τ → Δ  ⊢ᵣ simpl τ
    r-iabs : ∀ {ρ₁ ρ₂} → ((ρ₁ List.∷ Δ) ⊢ᵣ ρ₂) → Δ ⊢ᵣ (ρ₁ ⇒ ρ₂)
    r-tabs : ∀ {ρ} → ictx-weaken Δ ⊢ᵣ ρ → Δ ⊢ᵣ ∀' ρ
