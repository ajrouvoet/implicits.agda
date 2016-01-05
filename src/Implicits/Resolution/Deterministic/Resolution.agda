open import Prelude

module Implicits.Resolution.Deterministic.Resolution (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Data.Fin.Substitution
open import Implicits.Syntax TC _tc≟_
open import Implicits.Syntax.Type.Unification TC _tc≟_
open import Implicits.Substitutions TC _tc≟_

infixl 4 _⊢ᵣ_ _⊢_↓_ _⟨_⟩=_
infixl 6 _◁_

data _◁_ {ν} : Type ν → SimpleType ν → Set where
  m-simp : ∀ {a} → simpl a ◁ a
  m-tabs   : ∀ {a b r} → r tp[/tp b ] ◁ a → ∀' r ◁ a
  m-iabs   : ∀ {a b r} → r ◁ a → b ⇒ r ◁ a

data _⟨_⟩=_ {ν} : ∀ (Δ : ICtx ν) → SimpleType ν → Type ν → Set where
  l-head : ∀ {r a} → r ◁ a → (Δ : ICtx ν) → (r List.∷ Δ) ⟨ a ⟩= r
  l-tail : ∀ {Δ : ICtx ν} {r r' a} → ¬ (r ◁ a) → Δ ⟨ a ⟩= r' → (r List.∷ Δ) ⟨ a ⟩= r'

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

module FirstLemmas where

  first⟶∈ : ∀ {ν} {Δ : ICtx ν} {r a} → Δ ⟨ a ⟩= r → r List.∈ Δ × r ◁ a
  first⟶∈ (l-head px _) = here refl , px
  first⟶∈ (l-tail ¬px f) = (there (proj₁ px)) , proj₂ px
    where px = first⟶∈ f

  first-unique : ∀ {ν} {K : ICtx ν} {r r' a} → K ⟨ a ⟩= r → K ⟨ a ⟩= r' → r ≡ r'
  first-unique {K = List.[]} () y
  first-unique {K = x List.∷ .K} (l-head x₁ K) (l-head x₂ .K) = refl
  first-unique {K = x List.∷ .K} (l-head px K) (l-tail ¬px y) = ⊥-elim (¬px px)
  first-unique {K = r' List.∷ .K} (l-tail ¬px x₁) (l-head px K) = ⊥-elim (¬px px)
  first-unique {K = r₁ List.∷ Δ} (l-tail ¬px x) (l-tail ¬px' y) = first-unique x y

r↓a⟶r◁a : ∀ {ν} {K : ICtx ν} {r a} → K ⊢ r ↓ a → r ◁ a
r↓a⟶r◁a (i-simp a) = m-simp
r↓a⟶r◁a (i-iabs _ x) = m-iabs (r↓a⟶r◁a x)
r↓a⟶r◁a (i-tabs _ x) = m-tabs (r↓a⟶r◁a x)
