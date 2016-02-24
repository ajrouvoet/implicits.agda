open import Prelude

module Implicits.Resolution.Deterministic.Expressiveness where

open import Data.Fin.Substitution
open import Implicits.Syntax
open import Implicits.Syntax.Type.Unification
open import Implicits.Resolution.Ambiguous.Resolution as A
open import Implicits.Resolution.Deterministic.Resolution as D
open import Extensions.ListFirst

module Deterministic⊆Ambiguous where
  open FirstLemmas
  open import Relation.Unary

  soundness : ∀ {ν} {Δ : ICtx ν} {r} → Δ D.⊢ᵣ r → Δ A.⊢ᵣ r
  soundness (r-simp r x) = lem x (r-ivar (proj₁ $ first⟶∈ r))
    where
      lem : ∀ {ν} {a τ} {Δ : ICtx ν} → Δ ⊢ a ↓ τ → Δ A.⊢ᵣ a → Δ A.⊢ᵣ simpl τ
      lem (i-simp τ) hyp = hyp
      lem (i-iabs ih₁ ih₂) hyp = lem ih₂ (r-iapp hyp (soundness ih₁))
      lem (i-tabs b ih) hyp = lem ih (r-tapp b hyp)
  soundness (r-iabs _ ih) = r-iabs (soundness ih)
  soundness (r-tabs ih) = r-tabs (soundness ih)
