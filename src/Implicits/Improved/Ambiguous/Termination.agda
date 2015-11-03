open import Prelude

module Implicits.Improved.Ambiguous.Termination (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Coinduction
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Improved.Ambiguous.Resolution TC _tc≟_
open import Data.Nat
open import Size
open SyntaxDirected

mutual
  data ⊬div {ν} {Δ : ICtx ν} : ∀ {r τ} → Δ ⊢ r ↓ τ → Set where
    ndiv-simp : ∀ {r} → ⊬div (i-simp r)
    ndiv-iabs : ∀ {r₁ r₂ τ} (p : (Δ ⊢ᵣ r₁)) (d : Δ ⊢ r₂ ↓ τ) → r₁ ρ< r₂ → ⊬ᵣdiv p → ⊬div d →
                ⊬div (i-iabs (♯ p) d)
    ndiv-tabs : ∀ {r b τ} {x : Δ ⊢ (r tp[/tp b ]) ↓ τ} → ⊬div x →
                ⊬div (i-tabs {ρ = r} b x)

  data ⊬ᵣdiv {ν} {Δ : ICtx ν} : ∀ {r} → Δ ⊢ᵣ r → Set where
    ndiv-rsimp : ∀ {r τ r∈Δ} {r↓τ : Δ ⊢ r ↓ τ} → (x : ⊬div r↓τ) → ⊬ᵣdiv (r-simp r∈Δ r↓τ)
    ndiv-riabs : ∀ {r₁ r₂} {x : r₁ List.∷ Δ ⊢ᵣ r₂} → ⊬ᵣdiv x → ⊬ᵣdiv (r-iabs x)
    ndiv-rtabs : ∀ {r} {x : ictx-weaken Δ ⊢ᵣ r} → ⊬ᵣdiv x → ⊬ᵣdiv (r-tabs x)

  ⊢div : ∀ {ν} {Δ : ICtx ν} {r τ} → Δ ⊢ r ↓ τ → Set
  ⊢div x = ¬ ⊬div x

  ⊢ᵣdiv : ∀ {ν} {Δ : ICtx ν} {r} → Δ ⊢ᵣ r → Set
  ⊢ᵣdiv x = ¬ ⊬ᵣdiv x

  ?div : ∀ {ν} {Δ : ICtx ν} {a} → (x : Δ ⊢ᵣ a) → Dec (⊬ᵣdiv x)
  ?div (r-simp a b) with ?div' b
    where
      ?div' : ∀ {ν} {Δ : ICtx ν} {a τ} → (x : Δ ⊢ a ↓ τ) → Dec (⊬div x)
      ?div' (i-simp τ) = yes ndiv-simp
      ?div' (i-iabs {ρ₁ = r₁} {ρ₂ = r₂} ⊢r₁ r₂↓τ) with r₁ ρ<? r₂
      ?div' (i-iabs ⊢r₁ r₂↓τ) | yes p = {!!}
      ?div' (i-iabs ⊢r₁ r₂↓τ) | no ¬p = no (λ{ (ndiv-iabs p .r₂↓τ x x₁ x₂) → ? })
      ?div' (i-tabs b x) with ?div' x
      ?div' (i-tabs b x) | yes p = yes (ndiv-tabs p)
      ?div' (i-tabs b x) | no ¬p = no (λ{ (ndiv-tabs p) → ¬p p })
  ?div (r-simp a b) | yes p = yes (ndiv-rsimp p)
  ?div (r-simp a b) | no ¬p = no (λ{ (ndiv-rsimp x) → ¬p x })
  ?div (r-iabs x) with ?div x
  ?div (r-iabs x) | yes p = yes (ndiv-riabs p)
  ?div (r-iabs x) | no ¬p = no (λ{ (ndiv-riabs p) → ¬p p })
  ?div (r-tabs x) with ?div x
  ?div (r-tabs x) | yes p = yes (ndiv-rtabs p)
  ?div (r-tabs x) | no ¬p = no (λ{ (ndiv-rtabs p) → ¬p p })

module Example where
  tid : ∀ {n} → Type n
  tid = (∀' (simpl (tvar zero) ⇒ simpl (tvar zero)))

  tid↓a : ∀ {ν} {a : SimpleType ν} → (tid List.∷ List.[]) ⊢ tid ↓ a
  tid↓a {a = a} = i-tabs (simpl a) (i-iabs (♯ (r-simp (here refl) tid↓a)) (i-simp a))

  ⊢div[tid↓a] : ∀ {ν} {a : SimpleType ν} → ⊢div {ν} (tid↓a {a = a})
  ⊢div[tid↓a] (ndiv-tabs x) = {!x!}
