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

module SizeMeasure where
  open import Induction.WellFounded

  -- we can show that our size measure a ρ< b is well founded
  -- by relating it to the well-foundedness proof of _<'_
  ρ<-well-founded : ∀ {ν} → Well-founded (_ρ<_ {ν})
  ρ<-well-founded = sub.well-founded (image.well-founded <-well-founded)
    where
      open import Induction.Nat
      open import Data.Nat
      open import Data.Nat.Properties
      module sub = Inverse-image ||_||
      module image = Subrelation {A = ℕ} {_N<_} {_<′_} ≤⇒≤′

  -- Oliveira's size measure
  _ρ<'_ : ∀ {ν} → (a b : Type ν) → Set
  a ρ<' b = ∀ {τ₁ τ₂} → a ◁ τ₁ → b ◁ τ₂ → simpl τ₁ ρ< simpl τ₂

  {-
  ρ<'⇒ρ< : ∀ {ν} (a b : Type ν) → a ρ<' b → a ρ< b
  ρ<'⇒ρ< a b f = {!!}
  -}

  -- a, b such that ¬ a ρ< b × a ρ<' b
  a : Type (suc zero)
  a = (simpl (tvar zero) ⇒ simpl (tvar zero))
  b : Type (suc zero)
  b = (simpl (simpl (tvar zero) →' simpl (tvar zero)))

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

  {-
  p : ∀ {ν n} {a : Type ν} {K : Ktx ν n} → K D.⊢ᵣ a → (proj₂ K) I.⊢ᵣ a
  p (r-simp x r↓a) = r-simp (proj₁ $ FirstLemmas.first⟶∈ x) (lem r↓a)
  where
      lem : ∀ {ν n} {K : Ktx ν n} {r a} → K D.⊢ r ↓ a → (proj₂ K) I.⊢ r ↓ a
      lem (i-simp a) = i-simp a
      lem (i-iabs x₁ x₂) = i-iabs All.[] {!p x₁!} {!!}
      lem (i-tabs b x₁) = i-tabs b {!lem x₁!}
  p (r-iabs ρ₁ x) = r-iabs (p x)
  p (r-tabs x) = r-tabs (p x)
  -}
