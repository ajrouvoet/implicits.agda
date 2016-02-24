open import Prelude

module Implicits.Resolution.Infinite.NormalFormIso where

open import Implicits.Syntax
open import Implicits.Resolution.Infinite.Resolution
open import Implicits.Resolution.Ambiguous.Undecidable using (module Embedding; module Lemmas)
open import SystemF as F using ()
open import SystemF.NormalForm

open Embedding
open Lemmas

lookup-∈ : ∀ {ν n} → (x : Fin n) → (v : F.Ctx ν n) → ⟦ lookup x v ⟧tp← List.∈ ⟦ v ⟧ctx←
lookup-∈ zero (x ∷ xs) = here refl
lookup-∈ (suc x) (v ∷ vs) = there (lookup-∈ x vs) 

mutual

  from-⇓ : ∀ {ν n t a τ} {Γ : F.Ctx ν n} → Γ ⊢ t ⇓ a → ⟦ Γ ⟧ctx← ⊢ ⟦ a ⟧tp← ↓ τ →
           ∃ λ i → ⟦ Γ ⟧ctx← ⊢ ⟦ lookup i Γ ⟧tp← ↓ τ
  from-⇓ {Γ = Γ} (nvar i) ↓τ = i , ↓τ
  from-⇓ (napp p x) ↓τ = from-⇓ p (i-iabs (from-⇑ x) ↓τ)
  from-⇓ {Γ = Γ} (ntapp {a = a} b p) ↓τ = from-⇓ p
    (i-tabs ⟦ b ⟧tp← (subst (λ z → ⟦ Γ ⟧ctx← ⊢ z ↓ _) (⟦a/sub⟧tp← a b) ↓τ))

  from-⇑ : ∀ {ν n t a} {Γ : F.Ctx ν n} → Γ ⊢ t ⇑ a → ⟦ Γ ⟧ctx← ⊢ᵣ ⟦ a ⟧tp←
  from-⇑ (nvar x) with from-⇓ x (i-simp (tvar _))
  from-⇑ (nvar x) | i , lookup-i↓tc = r-simp (lookup-∈ i _) lookup-i↓tc
  from-⇑ (ntc x) with from-⇓ x (i-simp (tc _))
  from-⇑ (ntc x) | i , lookup-i↓tc = r-simp (lookup-∈ i _) lookup-i↓tc
  from-⇑ (nabs p) = r-iabs (from-⇑ p)
  from-⇑ (ntabs p) = r-tabs (subst (λ z → z ⊢ᵣ _) (⟦weaken⟧ctx← _) (from-⇑ p))
