open import Prelude

module Implicits.Resolution.GenericFinite.Resolution where

open import Coinduction
open import Data.Fin.Substitution
open import Relation.Binary using (Rel)

open import Implicits.Syntax
open import Implicits.Syntax.Type.Unification
open import Implicits.Substitutions
open import Implicits.Substitutions.Lemmas.MetaType
open import Implicits.Resolution.Termination
open import Implicits.Resolution.GenericFinite.TerminationCondition

private
  module M = MetaTypeMetaSubst

module ResolutionRules (cond : TerminationCondition) where
  open TerminationCondition cond

  mutual
    data _,_⊢_↓_ {ν} (Δ : ICtx ν) : (Φ : TCtx) → Type ν → SimpleType ν → Set where
      i-simp : ∀ {Φ} a → Δ , Φ ⊢ simpl a ↓ a
      i-iabs : ∀ {Φ ρ₁ ρ₂ a} → let Φ' = (step Φ Δ ρ₁ ρ₂ a) in
               Φ' < Φ → Δ , Φ' ⊢ᵣ ρ₁ → Δ , Φ ⊢ ρ₂ ↓ a → Δ , Φ ⊢ ρ₁ ⇒ ρ₂ ↓ a
      i-tabs : ∀ {Φ ρ a} b → Δ , Φ ⊢ ρ tp[/tp b ] ↓ a → Δ , Φ ⊢ ∀' ρ ↓ a

    data _,_⊢ᵣ_ {ν} (Δ : ICtx ν) : TCtx → Type ν → Set where
      r-simp : ∀ {Φ r τ} → r List.∈ Δ → Δ , Φ ⊢ r ↓ τ → Δ , Φ ⊢ᵣ simpl τ
      r-iabs : ∀ {Φ} ρ₁ {ρ₂} → ((ρ₁ List.∷ Δ) , Φ ⊢ᵣ ρ₂) → Δ , Φ ⊢ᵣ (ρ₁ ⇒ ρ₂)
      r-tabs : ∀ {Φ ρ} → ictx-weaken Δ , Φ ⊢ᵣ ρ → Δ , Φ ⊢ᵣ ∀' ρ
