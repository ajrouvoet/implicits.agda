open import Prelude

module Implicits.Improved.Finite.Expressiveness (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Coinduction
open import Data.Fin.Substitution
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.Deterministic.Resolution TC _tc≟_ as D
open import Implicits.Oliveira.Ambiguous.Resolution TC _tc≟_ as A
open import Implicits.Improved.Finite.Resolution TC _tc≟_ as F
open import Implicits.Improved.Infinite.Resolution TC _tc≟_ as ∞

module Finite⊆Infinite where

  p : ∀ {ν} {a s} {Δ : ICtx ν} → Δ F.& s ⊢ᵣ a → Δ ∞.⊢ᵣ a
  p (r-simp a a↓τ) = r-simp a (lem a↓τ)
    where
      lem : ∀ {ν} {a r τ s} {Δ : ICtx ν} → Δ F.& s , r ⊢ a ↓ τ → Δ ∞.⊢ a ↓ τ
      lem (i-simp τ) = i-simp τ
      lem (i-iabs _ ⊢ᵣa b↓τ) = i-iabs (♯ (p ⊢ᵣa)) (lem b↓τ)
      lem (i-tabs b a[/b]↓τ) = i-tabs b (lem a[/b]↓τ)
  p (r-iabs x) = r-iabs (p x)
  p (r-tabs x) = r-tabs (p x)

module Finite⊆OliveiraAmbiguous where

  p : ∀ {ν n} {a s} {K : Ktx ν n} → (proj₂ K) F.& s ⊢ᵣ a → K A.⊢ᵣ a
  p (r-simp a a↓τ) = lem a↓τ (r-ivar a)
    where
      lem : ∀ {ν n} {a r τ s} {K : Ktx ν n} →
            (proj₂ K) F.& s , r ⊢ a ↓ τ → K A.⊢ᵣ a → K A.⊢ᵣ simpl τ
      lem (i-simp τ) K⊢ᵣτ = K⊢ᵣτ
      lem (i-iabs _ ⊢ᵣa b↓τ) K⊢ᵣa⇒b = lem b↓τ (r-iapp K⊢ᵣa⇒b (p ⊢ᵣa))
      lem (i-tabs b a[/b]↓τ) K⊢ᵣ∀a = lem a[/b]↓τ (r-tapp b K⊢ᵣ∀a)
  p (r-iabs x) = r-iabs (p x)
  p (r-tabs x) = r-tabs (p x)

module OliveiraDeterministic⊆Finite where

  -- Oliveira's termination condition is part of the well-formdness of types
  -- So we assume here that ⊢term x holds for all types x
  p : ∀ {ν n} {a : Type ν} {K : Ktx ν n} s →
      (∀ {μ} (x : Type μ) → ⊢term x) → K D.⊢ᵣ a → (proj₂ K) F.& s ⊢ᵣ a
  p s term (r-simp {ρ = r} x r↓a) = r-simp (proj₁ $ FirstLemmas.first⟶∈ x) (lem r s r↓a)
    where
      lem : ∀ {ν n} {K : Ktx ν n} r∈Δ {r a} s → K D.⊢ r ↓ a → (proj₂ K) F.& s , r∈Δ ⊢ r ↓ a
      lem r∈Δ s (i-simp a) = i-simp a
      lem r∈Δ s (i-iabs {ρ₁ = ρ₁} ⊢ᵣρ₁ ρ₂↓τ) =
        i-iabs {!!} (p ((r∈Δ , ρ₁) List.∷ s) term ⊢ᵣρ₁) (lem r∈Δ s ρ₂↓τ)
      lem r∈Δ s (i-tabs b x₁) = i-tabs b (lem r∈Δ s x₁)
  p s term (r-iabs ρ₁ x) = r-iabs (p s term x)
  p s term (r-tabs x) = r-tabs (p (stack-weaken s) term x)
