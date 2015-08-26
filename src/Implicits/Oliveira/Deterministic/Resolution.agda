open import Prelude

module Implicits.Oliveira.Deterministic.Resolution (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Data.Fin.Substitution
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Types.Unification TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Extensions.ListFirst

infixl 4 _⊢ᵣ_ _⊢_↓_ _⟨_⟩=_
infixl 6 _◁_

data _◁_ {ν} : Type ν → SimpleType ν → Set where
  m-simp : ∀ {a} → simpl a ◁ a
  m-tabs   : ∀ {a b r} → r tp[/tp b ] ◁ a → ∀' r ◁ a
  m-iabs   : ∀ {a b r} → r ◁ a → b ⇒ r ◁ a

-- implicit resolution is simply the first rule in the implicit context
-- that yields the queried type
_⟨_⟩=_ : ∀ {ν n} → Ktx ν n → SimpleType ν → Type ν → Set
(Γ , Δ) ⟨ a ⟩= r = first r ∈ Δ ⇔ (λ r' → r' ◁ a)

mutual 
  data _⊢_↓_ {ν n} (K : Ktx ν n) : Type ν → SimpleType ν → Set where
    i-simp : ∀ a → K ⊢ simpl a ↓ a
    i-iabs : ∀ {ρ₁ ρ₂ a} → K ⊢ᵣ ρ₁ → K ⊢ ρ₂ ↓ a → K ⊢ ρ₁ ⇒ ρ₂ ↓ a
    i-tabs : ∀ {ρ a} b → K ⊢ ρ tp[/tp b ] ↓ a → K ⊢ ∀' ρ ↓ a

  data _⊢ᵣ_ {ν n} (K : Ktx ν n) : Type ν → Set where
    r-simp : ∀ {τ ρ} → K ⟨ τ ⟩= ρ → K ⊢ ρ ↓ τ → K ⊢ᵣ simpl τ
    r-iabs : ∀ ρ₁ {ρ₂} → ρ₁ ∷K K ⊢ᵣ ρ₂ → K ⊢ᵣ ρ₁ ⇒ ρ₂
    r-tabs : ∀ {ρ} → ktx-weaken K ⊢ᵣ ρ → K ⊢ᵣ ∀' ρ

