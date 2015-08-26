open import Prelude

module Implicits.Oliveira.Ambiguous.Resolution (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Data.Fin.Substitution
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Types.Unification TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Extensions.ListFirst

data _⊢ᵣ_ {ν n} (K : Ktx ν n) : Type ν → Set where
  r-tabs : ∀ {r} → ktx-weaken K ⊢ᵣ r → K ⊢ᵣ ∀' r
  r-tapp : ∀ {a r} → K ⊢ᵣ ∀' r → K ⊢ᵣ (r tp[/tp a ])
  r-ivar : ∀ {r} → r List.∈ proj₂ K → K ⊢ᵣ r
  r-iabs : ∀ {a b} → (a ∷K K) ⊢ᵣ b → K ⊢ᵣ (a ⇒ b)
  r-iapp : ∀ {a b} → K ⊢ᵣ (a ⇒ b) → K ⊢ᵣ a → K ⊢ᵣ b
