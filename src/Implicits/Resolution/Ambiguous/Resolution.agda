open import Prelude

module Implicits.Resolution.Ambiguous.Resolution (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Data.Fin.Substitution
open import Implicits.Syntax TC _tc≟_
open import Implicits.Substitutions TC _tc≟_

data _⊢ᵣ_ {ν} (Δ : ICtx ν) : Type ν → Set where
  r-tabs : ∀ {r} → ictx-weaken Δ ⊢ᵣ r → Δ ⊢ᵣ ∀' r
  r-tapp : ∀ {r} a → Δ ⊢ᵣ ∀' r → Δ ⊢ᵣ (r tp[/tp a ])
  r-ivar : ∀ {r} → r List.∈ Δ → Δ ⊢ᵣ r
  r-iabs : ∀ {a b} → (a List.∷ Δ) ⊢ᵣ b → Δ ⊢ᵣ (a ⇒ b)
  r-iapp : ∀ {a b} → Δ ⊢ᵣ (a ⇒ b) → Δ ⊢ᵣ a → Δ ⊢ᵣ b

data _⊢normal {ν} {Δ : ICtx ν} : ∀ {r} → (Δ ⊢ᵣ r) → Set where
  n-ivar : ∀ {r} {r∈Δ : r List.∈ Δ} → (r-ivar r∈Δ) ⊢normal
  n-tabs : ∀ {r} {p : (ictx-weaken Δ) ⊢ᵣ r} →
           p ⊢normal → (r-tabs p) ⊢normal
  n-tapp : ∀ {r} b → (r∈Δ : (∀' r) List.∈ Δ) → (r-tapp b (r-ivar r∈Δ)) ⊢normal
  n-iapp : ∀ {a b e} → (f : (a ⇒ b) List.∈ Δ) → e ⊢normal →
           (r-iapp (r-ivar f) e) ⊢normal
  n-iabs : ∀ {a b} {e : (a List.∷ Δ) ⊢ᵣ b} →
           e ⊢normal → (r-iabs e) ⊢normal
