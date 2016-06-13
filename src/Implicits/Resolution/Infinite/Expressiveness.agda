module Implicits.Resolution.Infinite.Expressiveness where

open import Prelude hiding (Bool)

open import Data.Fin.Substitution

open import Extensions.ListFirst
open import SystemF as F using ()

open import Implicits.Resolution.Ambiguous.Resolution as A
open import Implicits.Resolution.Deterministic.Resolution as D
open import Implicits.Resolution.Infinite.Resolution as I
open import Implicits.Syntax
open import Implicits.Substitutions

module Deterministic⊆Infinite where

  complete : ∀ {ν} {a : Type ν} {Δ : ICtx ν} → Δ D.⊢ᵣ a → Δ I.⊢ᵣ a
  complete (r-simp x r↓a) = r-simp (proj₁ $ first⟶∈ x) (lem r↓a)
    where
      lem : ∀ {ν} {Δ : ICtx ν} {r a} → Δ D.⊢ r ↓ a → Δ I.⊢ r ↓ a
      lem (i-simp a) = i-simp a
      lem (i-iabs x₁ x₂) = i-iabs (complete x₁) (lem x₂)
      lem (i-tabs b x₁) = i-tabs b (lem x₁)
  complete (r-iabs ρ₁ x) = r-iabs (complete x)
  complete (r-tabs x) = r-tabs (complete x)

module Deterministic⊂Infinite where

  open import Implicits.Resolution.Deterministic.Incomplete as Inc

  -- We gave an example of a query that the det rules could not resolve
  --   ((Int ⇒ Bool) List.∷ Bool List.∷ List.[]) ⊢ᵣ Bool
  -- Here we derive it for the Infinite rules, to prove that we are strictly
  -- more expressive
  infinite-can : Δ I.⊢ᵣ Bool
  infinite-can = r-simp (there (here refl)) p
    where
      p : Δ I.⊢ Bool ↓ tc 0
      p = i-simp (tc 0)

module Infinite⇔Ambiguous
  (nf : ∀ {ν n} {Γ : F.Ctx ν n} {t a} → Γ F.⊢ t ∈ a → ∃ λ (t₂ : F.Term ν n) → Γ F.⊢ t₂ ⇑ a)
  where

  open import Implicits.Resolution.Ambiguous.SystemFEquiv hiding (equivalent)
  open import Implicits.Resolution.Infinite.NormalFormEquiv hiding (equivalent)
  open import Implicits.Resolution.Embedding.Lemmas
  open import Function.Equivalence

  sound : ∀ {ν} {a : Type ν} {Δ : ICtx ν} → Δ I.⊢ᵣ a → Δ A.⊢ᵣ a
  sound (r-simp x p) = lem p (r-ivar x)
    where
      lem : ∀ {ν} {Δ : ICtx ν} {a τ} → Δ I.⊢ a ↓ τ → Δ A.⊢ᵣ a → Δ A.⊢ᵣ (simpl τ)
      lem (i-simp τ) ⊢y = ⊢y
      lem (i-iabs ⊢a b↓τ) ⊢b = lem b↓τ (r-iapp ⊢b (sound ⊢a))
      lem (i-tabs b a) ⊢y = lem a (r-tapp b ⊢y)
  sound (r-iabs p) = r-iabs (sound p)
  sound (r-tabs p) = r-tabs (sound p)

  complete : ∀ {ν} {a : Type ν} {Δ : ICtx ν} → Δ A.⊢ᵣ a → Δ I.⊢ᵣ a
  complete {a = a} p = subst₂ (λ Δ r → Δ I.⊢ᵣ r) (ctx→← _) (tp→← a) (from-⇑ (proj₂ (nf (to-⊢ p))))

  equivalent : ∀ {ν} (Δ : ICtx ν) r → Δ I.⊢ᵣ r ⇔ Δ A.⊢ᵣ r
  equivalent Δ r = equivalence sound complete
