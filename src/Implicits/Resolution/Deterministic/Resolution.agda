open import Prelude

module Implicits.Resolution.Deterministic.Resolution where

open import Data.Fin.Substitution
open import Implicits.Syntax
open import Implicits.Syntax.Type.Unification
open import Implicits.Substitutions
open import Extensions.ListFirst

infixl 4 _⊢ᵣ_ _⊢_↓_ _⟨_⟩=_
infixl 6 _◁_

data _◁_ {ν} : Type ν → SimpleType ν → Set where
  m-simp : ∀ {a} → simpl a ◁ a
  m-tabs   : ∀ {a r} b → r tp[/tp b ] ◁ a → ∀' r ◁ a
  m-iabs   : ∀ {a b r} → r ◁ a → b ⇒ r ◁ a

_⟨_⟩=_ : ∀ {ν} (Δ : ICtx ν) → SimpleType ν → Type ν → Set
Δ ⟨ τ ⟩= r = first r ∈ Δ ⇔ (flip _◁_ τ)

mutual 
  data _⊢_↓_ {ν} (K : ICtx ν) : Type ν → SimpleType ν → Set where
    i-simp : ∀ a → K ⊢ simpl a ↓ a
    i-iabs : ∀ {ρ₁ ρ₂ a} → K ⊢ᵣ ρ₁ → K ⊢ ρ₂ ↓ a → K ⊢ ρ₁ ⇒ ρ₂ ↓ a
    i-tabs : ∀ {ρ a} b → K ⊢ ρ tp[/tp b ] ↓ a → K ⊢ ∀' ρ ↓ a

  data _⊢ᵣ_ {ν} (K : ICtx ν) : Type ν → Set where
    r-simp : ∀ {τ ρ} → K ⟨ τ ⟩= ρ → K ⊢ ρ ↓ τ → K ⊢ᵣ simpl τ
    r-iabs : ∀ ρ₁ {ρ₂} → ρ₁ List.∷ K ⊢ᵣ ρ₂ → K ⊢ᵣ ρ₁ ⇒ ρ₂
    r-tabs : ∀ {ρ} → ictx-weaken K ⊢ᵣ ρ → K ⊢ᵣ ∀' ρ

_⊢ᵣ[_] : ∀ {ν} → (K : ICtx ν) → List (Type ν) → Set
_⊢ᵣ[_] K ρs = All (λ r → K ⊢ᵣ r) ρs

r↓a⟶r◁a : ∀ {ν} {K : ICtx ν} {r a} → K ⊢ r ↓ a → r ◁ a
r↓a⟶r◁a (i-simp a) = m-simp
r↓a⟶r◁a (i-iabs _ x) = m-iabs (r↓a⟶r◁a x)
r↓a⟶r◁a (i-tabs b x) = m-tabs b (r↓a⟶r◁a x)
