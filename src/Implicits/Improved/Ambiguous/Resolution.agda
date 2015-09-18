open import Prelude

module Implicits.Improved.Ambiguous.Resolution (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Coinduction
open import Data.Fin.Substitution
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_

data _⊢ᵣ_ {ν} (Δ : ICtx ν) : Type ν → Set where
  r-tabs : ∀ {r} → ∞ (ictx-weaken Δ ⊢ᵣ r) → Δ ⊢ᵣ ∀' r
  r-tapp : ∀ {r} a → ∞ (Δ ⊢ᵣ ∀' r) → Δ ⊢ᵣ (r tp[/tp a ])
  r-ivar : ∀ {r} → r List.∈ Δ → Δ ⊢ᵣ r
  r-iabs : ∀ {a b} → ∞ ((a List.∷ Δ) ⊢ᵣ b) → Δ ⊢ᵣ (a ⇒ b)
  r-iapp : ∀ {a b} → ∞ (Δ ⊢ᵣ (a ⇒ b)) → ∞ (Δ ⊢ᵣ a) → Δ ⊢ᵣ b

module IdDerives where
  -- proof that polymorphic id derives every type
  -- this corresponds to the non-terminating expression:
  --   x : ∀ {a : Set} → a
  --   x = x

  tid : ∀ {n} → Type n
  tid = (∀' (simpl (tvar zero) ⇒ simpl (tvar zero)))

  [tid]⊢a : ∀ {ν} {a : Type ν} → (tid List.∷ List.[]) ⊢ᵣ a
  [tid]⊢a {a = a} = r-iapp (♯ (r-tapp a (♯ (r-ivar (here refl))))) (♯ [tid]⊢a)

  -- we can even derive it from an empty context, because we can derive identity from nothing:
  []⊢tid : ∀ {ν} → List.[] ⊢ᵣ tid {ν}
  []⊢tid = r-tabs (♯ (r-iabs (♯ (r-ivar (here refl)))))

  []⊢a : ∀ {ν} {a : Type ν} → List.[] ⊢ᵣ a
  []⊢a {a} = r-iapp (♯ r-iabs (♯ [tid]⊢a)) (♯ []⊢tid)
