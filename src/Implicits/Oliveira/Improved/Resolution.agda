{-# OPTIONS --no-positivity-check #-}
open import Prelude

module Implicits.Oliveira.Improved.Resolution (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Data.Fin.Substitution
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Types.Unification TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Extensions.ListFirst

infixl 4 _⊢ᵣ_ _⊢_↓_ _⟨_⟩=_

mutual 
  data _⊢_↓_ {ν n} (K : Ktx ν n) : Type ν → SimpleType ν → Set where
    i-simp : ∀ a → K ⊢ simpl a ↓ a
    i-iabs : ∀ {ρ₁ ρ₂ a} → K ⊢ᵣ ρ₁ → K ⊢ ρ₂ ↓ a → K ⊢ ρ₁ ⇒ ρ₂ ↓ a
    i-tabs : ∀ {ρ a} b → K ⊢ ρ tp[/tp b ] ↓ a → K ⊢ ∀' ρ ↓ a

  -- implicit resolution is simply the first rule in the implicit context
  -- that yields the queried type
  _⟨_⟩=_ : ∀ {ν n} → Ktx ν n → SimpleType ν → Type ν → Set
  (Γ , Δ) ⟨ a ⟩= r = first r ∈ Δ ⇔ (λ r' → (Γ , Δ) ⊢ r' ↓ a)

  data _⊢ᵣ_ {ν n} (K : Ktx ν n) : Type ν → Set where
    r-simp : ∀ {τ ρ} → K ⟨ τ ⟩= ρ → K ⊢ᵣ simpl τ
    r-iabs : ∀ ρ₁ {ρ₂} → ρ₁ ∷K K ⊢ᵣ ρ₂ → K ⊢ᵣ ρ₁ ⇒ ρ₂
    r-tabs : ∀ {ρ} → ktx-weaken K ⊢ᵣ ρ → K ⊢ᵣ ∀' ρ

_⊢ᵣ[_] : ∀ {ν n} → (K : Ktx ν n) → List (Type ν) → Set
_⊢ᵣ[_] K ρs = All (λ r → K ⊢ᵣ r) ρs
