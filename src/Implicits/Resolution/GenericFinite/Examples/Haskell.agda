open import Prelude hiding (_≤_)
open import Data.Nat.Properties
open import Induction.Nat

module Implicits.Resolution.GenericFinite.Examples.Haskell
  where

open import Implicits.Resolution.GenericFinite.TerminationCondition
open import Implicits.Resolution.GenericFinite.Resolution
open import Implicits.Resolution.GenericFinite.Algorithm
open import Implicits.Syntax
open import Implicits.Syntax.Type.Unification
open import Implicits.Resolution.Termination
open import Implicits.Substitutions

haskellCondition : TerminationCondition
haskellCondition = record
  { TCtx = ∃ Type
  ; _<_  = _hρ<_
  ; _<?_  = λ { (_ , x) (_ , y) → x hρ<? y }
  ; step = λ Φ Δ a b τ → , a
  ; wf-< = hρ<-well-founded
  }

open ResolutionRules haskellCondition public
open ResolutionAlgorithm haskellCondition public

module Deterministic⊆HaskellFinite where
  open import Implicits.Resolution.Deterministic.Resolution as D
  open import Data.Nat hiding (_<_)
  open import Data.Nat.Properties
  open import Relation.Binary using (module DecTotalOrder)
  open import Extensions.ListFirst
  open DecTotalOrder decTotalOrder using () renaming (refl to ≤-refl; trans to ≤-trans)
  module F = ResolutionRules haskellCondition
  module M = MetaTypeMetaSubst

  lem₆ : ∀ {ν μ} (a : Type ν) (b : Type (suc μ)) c → (, a) hρ< (, b) → (, a) hρ< (, b tp[/tp c ])
  lem₆ a b c p = ≤-trans p (h||a/s|| b (TypeSubst.sub c))
    where open SubstSizeLemmas

  lem₅ : ∀ {ν μ} {Δ : ICtx ν} {b τ} (a : Type μ) → Δ ⊢ b ↓ τ → (, a) hρ< (, b) → (, a) hρ< (, simpl τ)
  lem₅ {τ = τ} a (i-simp .τ) q = q
  lem₅ a (i-iabs _ p) q = lem₅ a p q
  lem₅ a (i-tabs {ρ = b} c p) q = lem₅ a p (lem₆ a b c q)

  -- Oliveira's termination condition is part of the well-formdness of types
  -- So we assume here that ⊢term x holds for all types x
  mutual
    lem : ∀ {ν} {Δ : ICtx ν} {a r g} →
          (∀ {ν} (a : Type ν) → ⊢term a) →
          (, simpl a) hρ≤ g → Δ D.⊢ r ↓ a → Δ F., g ⊢ r ↓ a
    lem all-⊢term q (i-simp a) = i-simp a
    lem {a = a} {g = g}all-⊢term q (i-iabs {ρ₁ = ρ₁} {ρ₂ = ρ₂} ⊢ρ₁ ρ₂↓a) with all-⊢term (ρ₁ ⇒ ρ₂)
    lem {a = a} {g = g} all-⊢term q (i-iabs {ρ₁ = ρ₁} {ρ₂ = ρ₂} ⊢ρ₁ ρ₂↓a) | term-iabs _ _ a-hρ<-b _ =
      i-iabs ρ₁<g (complete' (, ρ₁) all-⊢term ⊢ρ₁ ≤-refl) (lem all-⊢term q ρ₂↓a)
      where
        ρ₁<g : (, ρ₁) hρ< g
        ρ₁<g = ≤-trans (lem₅ ρ₁ ρ₂↓a a-hρ<-b) q
    lem all-⊢term q (i-tabs b p) = i-tabs b (lem all-⊢term q p)

    complete' : ∀ {ν} {a : Type ν} {Δ : ICtx ν} → (g : ∃ Type) →
              (∀ {ν} (a : Type ν) → ⊢term a) → Δ D.⊢ᵣ a → (, a) hρ≤ g →
              Δ F., g ⊢ᵣ a
    complete' g all-⊢term (r-simp x p) q = r-simp (proj₁ $ first⟶∈ x) (lem all-⊢term q p)
    complete' g all-⊢term (r-iabs ρ₁ p) q = r-iabs ρ₁ (complete' g all-⊢term p q)
    complete' g all-⊢term (r-tabs p) q = r-tabs (complete' g all-⊢term p q)

  complete : ∀ {ν} {a : Type ν} {Δ : ICtx ν} →
            (∀ {ν} (a : Type ν) → ⊢term a) → Δ D.⊢ᵣ a → Δ F., (, a) ⊢ᵣ a
  complete all-⊢term p = complete' _ all-⊢term p ≤-refl
