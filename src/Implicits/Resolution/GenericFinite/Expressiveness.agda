open import Prelude

module Implicits.Resolution.GenericFinite.Expressiveness
  where

open import Coinduction
open import Data.Fin.Substitution
open import Implicits.Syntax
open import Implicits.Substitutions
open import Implicits.Resolution.Deterministic.Resolution as D
open import Implicits.Resolution.Ambiguous.Resolution as A
open import Implicits.Resolution.Finite.Resolution as F
open import Implicits.Resolution.Infinite.Resolution as ∞
open import Implicits.Resolution.Termination
open import Extensions.ListFirst

module Finite⊆Infinite where

  p : ∀ {ν} {a} {Δ : ICtx ν} → Δ F.⊢ᵣ a → Δ ∞.⊢ᵣ a
  p (r-simp a a↓τ) = r-simp a (lem a↓τ)
    where
      lem : ∀ {ν} {a τ} {Δ : ICtx ν} → Δ F.⊢ a ↓ τ → Δ ∞.⊢ a ↓ τ
      lem (i-simp τ) = i-simp τ
      lem (i-iabs _ ⊢ᵣa b↓τ) = i-iabs (p ⊢ᵣa) (lem b↓τ)
      lem (i-tabs b a[/b]↓τ) = i-tabs b (lem a[/b]↓τ)
  p (r-iabs x) = r-iabs (p x)
  p (r-tabs x) = r-tabs (p x)

module Finite⊆Ambiguous where

  p : ∀ {ν} {a} {Δ : ICtx ν} → Δ F.⊢ᵣ a → Δ A.⊢ᵣ a
  p (r-simp a a↓τ) = lem a↓τ (r-ivar a)
    where
      lem : ∀ {ν} {a τ} {Δ : ICtx ν} → Δ F.⊢ a ↓ τ → Δ A.⊢ᵣ a → Δ A.⊢ᵣ simpl τ
      lem (i-simp τ) K⊢ᵣτ = K⊢ᵣτ
      lem (i-iabs _ ⊢ᵣa b↓τ) K⊢ᵣa⇒b = lem b↓τ (r-iapp K⊢ᵣa⇒b (p ⊢ᵣa))
      lem (i-tabs b a[/b]↓τ) K⊢ᵣ∀a = lem a[/b]↓τ (r-tapp b K⊢ᵣ∀a)
  p (r-iabs x) = r-iabs (p x)
  p (r-tabs x) = r-tabs (p x)

module Deterministic⊆Finite where

  open FirstLemmas

  -- Oliveira's termination condition is part of the well-formdness of types
  -- So we assume here that ⊢term x holds for all types x
  p : ∀ {ν} {a : Type ν} {Δ : ICtx ν} → (∀ {ν} (a : Type ν) → ⊢term a) → Δ D.⊢ᵣ a → Δ F.⊢ᵣ a
  p term (r-simp {ρ = r} x r↓a) =
    r-simp (proj₁ $ first⟶∈ x) (lem r↓a)
    where
      lem : ∀ {ν} {Δ : ICtx ν} {a r} → Δ D.⊢ r ↓ a → Δ F.⊢ r ↓ a
      lem (i-simp a) = i-simp a
      lem (i-iabs {ρ₁ = ρ₁} {ρ₂ = ρ₂} ⊢ᵣρ₁ ρ₂↓τ) with term (ρ₁ ⇒ ρ₂)
      lem (i-iabs ⊢ᵣρ₁ ρ₂↓τ) | term-iabs _ _ a-ρ<-b _ = i-iabs a-ρ<-b (p term ⊢ᵣρ₁) (lem ρ₂↓τ)
      lem (i-tabs b x₁) = i-tabs b (lem x₁)
  p term (r-iabs ρ₁ {ρ₂ = ρ₂} x) = r-iabs (p term x)
  p term (r-tabs x) = r-tabs (p term x)
