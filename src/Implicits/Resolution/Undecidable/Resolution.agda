{-# OPTIONS --no-positivity-check #-}
open import Prelude

module Implicits.Resolution.Undecidable.Resolution where

open import Data.Fin.Substitution
open import Implicits.Syntax
open import Implicits.Syntax.MetaType
open import Implicits.Substitutions
open import Extensions.ListFirst

infixl 4 _⊢ᵣ_ _⊢_↓_ _⟨_⟩=_

mutual 
  data _⊢_↓_ {ν} (Δ : ICtx ν) : Type ν → SimpleType ν → Set where
    i-simp : ∀ a → Δ ⊢ simpl a ↓ a
    i-iabs : ∀ {ρ₁ ρ₂ a} → Δ ⊢ᵣ ρ₁ → Δ ⊢ ρ₂ ↓ a → Δ ⊢ ρ₁ ⇒ ρ₂ ↓ a
    i-tabs : ∀ {ρ a} b → Δ ⊢ ρ tp[/tp b ] ↓ a → Δ ⊢ ∀' ρ ↓ a

  -- implicit resolution is simply the first rule in the implicit context
  -- that yields the queried type
  _⟨_⟩=_ : ∀ {ν} → ICtx ν → SimpleType ν → Type ν → Set
  Δ ⟨ a ⟩= r = first r ∈ Δ ⇔ (λ r' → Δ ⊢ r' ↓ a)

  data _⊢ᵣ_ {ν} (Δ : ICtx ν) : Type ν → Set where
    r-simp : ∀ {τ ρ} → Δ ⟨ τ ⟩= ρ → Δ ⊢ᵣ simpl τ
    r-iabs : ∀ ρ₁ {ρ₂} → ρ₁ List.∷ Δ ⊢ᵣ ρ₂ → Δ ⊢ᵣ ρ₁ ⇒ ρ₂
    r-tabs : ∀ {ρ} → ictx-weaken Δ ⊢ᵣ ρ → Δ ⊢ᵣ ∀' ρ

_⊢ᵣ[_] : ∀ {ν} → (Δ : ICtx ν) → List (Type ν) → Set
_⊢ᵣ[_] Δ ρs = All (λ r → Δ ⊢ᵣ r) ρs

