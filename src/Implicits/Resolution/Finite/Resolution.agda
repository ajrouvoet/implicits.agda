open import Prelude

module Implicits.Resolution.Finite.Resolution where

open import Coinduction
open import Data.Fin.Substitution
open import Data.List
open import Data.List.Any
open Membership-≡
open import Implicits.Syntax
open import Implicits.Substitutions
open import Implicits.Resolution.Termination
open import Induction
open import Induction.Nat
open import Relation.Binary using (Rel)

mutual

  data _⊢_↓_ {ν} (Δ : ICtx ν) : Type ν → SimpleType ν → Set where
    i-simp : ∀ a → Δ ⊢ simpl a ↓ a
    i-iabs : ∀ {ρ₁ ρ₂ a} → (, ρ₁) hρ< (, ρ₂) → Δ ⊢ᵣ ρ₁ → Δ ⊢ ρ₂ ↓ a → Δ ⊢ ρ₁ ⇒ ρ₂ ↓ a
    i-tabs : ∀ {ρ a} b → Δ ⊢ ρ tp[/tp b ] ↓ a → Δ ⊢ ∀' ρ ↓ a

  data _⊢ᵣ_ {ν} (Δ : ICtx ν) : Type ν → Set where
    r-simp : ∀ {r τ} → r ∈ Δ → Δ ⊢ r ↓ τ → Δ  ⊢ᵣ simpl τ
    r-iabs : ∀ {ρ₁ ρ₂} → ((ρ₁ ∷ Δ) ⊢ᵣ ρ₂) → Δ ⊢ᵣ (ρ₁ ⇒ ρ₂)
    r-tabs : ∀ {ρ} → ictx-weaken Δ ⊢ᵣ ρ → Δ ⊢ᵣ ∀' ρ
