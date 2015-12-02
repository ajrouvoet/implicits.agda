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

  p : ∀ {ν} {a} {Δ : ICtx ν} {s} → Δ F.& s ⊢ᵣ a → Δ ∞.⊢ᵣ a
  p (r-simp a a↓τ) = r-simp a (lem a↓τ)
    where
      lem : ∀ {ν} {a τ r} {Δ : ICtx ν} {r∈Δ : r List.∈ Δ} {s : Stack Δ} →
            Δ F.& s , r∈Δ ⊢ a ↓ τ → Δ ∞.⊢ a ↓ τ
      lem (i-simp τ) = i-simp τ
      lem (i-iabs _ ⊢ᵣa b↓τ) = i-iabs (♯ (p ⊢ᵣa)) (lem b↓τ)
      lem (i-tabs b a[/b]↓τ) = i-tabs b (lem a[/b]↓τ)
  p (r-iabs x) = r-iabs (p x)
  p (r-tabs x) = r-tabs (p x)

module Finite⊆OliveiraAmbiguous where

  p : ∀ {ν} {a} {Δ : ICtx ν} {s} → Δ F.& s ⊢ᵣ a → Δ A.⊢ᵣ a
  p (r-simp a a↓τ) = lem a↓τ (r-ivar a)
    where
      lem : ∀ {ν} {a r τ} {Δ : ICtx ν} {r∈Δ : r List.∈ Δ} {s} →
            Δ F.& s , r∈Δ ⊢ a ↓ τ → Δ A.⊢ᵣ a → Δ A.⊢ᵣ simpl τ
      lem (i-simp τ) K⊢ᵣτ = K⊢ᵣτ
      lem (i-iabs _ ⊢ᵣa b↓τ) K⊢ᵣa⇒b = lem b↓τ (r-iapp K⊢ᵣa⇒b (p ⊢ᵣa))
      lem (i-tabs b a[/b]↓τ) K⊢ᵣ∀a = lem a[/b]↓τ (r-tapp b K⊢ᵣ∀a)
  p (r-iabs x) = r-iabs (p x)
  p (r-tabs x) = r-tabs (p x)

module OliveiraDeterministic⊆Finite where

  open FirstLemmas

  -- Oliveira's termination condition is part of the well-formdness of types
  -- So we assume here that ⊢term x holds for all types x
  p : ∀ {ν} {a : Type ν} {Δ : ICtx ν} s →
      (∀ {μ} (x : Type μ) → ⊢term x) → Δ D.⊢ᵣ a → Δ F.& s ⊢ᵣ a
  p s term (r-simp {ρ = r} x r↓a) =
    r-simp (proj₁ $ FirstLemmas.first⟶∈ x) (lem (proj₁ $ first⟶∈ x) s r↓a)
    where
      lem : ∀ {ν r'} {Δ : ICtx ν} (r∈Δ : r' List.∈ Δ) {a r} s → Δ D.⊢ r ↓ a → Δ F.& s , r∈Δ ⊢ r ↓ a
      lem r∈Δ s (i-simp a) = i-simp a
      lem r∈Δ s (i-iabs {ρ₁ = ρ₁} ⊢ᵣρ₁ ρ₂↓τ) =
        i-iabs (push< s r∈Δ {!!}) (p (s push ρ₁ for r∈Δ) term ⊢ᵣρ₁) (lem r∈Δ s ρ₂↓τ)
      lem r∈Δ s (i-tabs b x₁) = i-tabs b (lem r∈Δ s x₁)
  p s term (r-iabs ρ₁ {ρ₂ = ρ₂} x) = r-iabs (p (s prepend ρ₂) term x)
  p s term (r-tabs x) = r-tabs (p (stack-weaken s) term x)
