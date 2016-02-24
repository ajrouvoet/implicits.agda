open import Prelude hiding (Bool)

module Implicits.Resolution.Infinite.Expressiveness where

open import Data.Fin.Substitution
open import Extensions.ListFirst

module Deterministic⊆Infinite where

  open import Implicits.Resolution.Deterministic.Resolution as D
  open import Implicits.Resolution.Infinite.Resolution as I
  open import Implicits.Syntax
  open import Implicits.Substitutions

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
  open import Implicits.Resolution.Deterministic.Resolution as D
  open import Implicits.Resolution.Infinite.Resolution as I
  open import Implicits.Syntax

  -- We gave an example of a query that the det rules could not resolve
  --   ((Int ⇒ Bool) List.∷ Bool List.∷ List.[]) ⊢ᵣ Bool
  -- Here we derive it for the Infinite rules, to prove that we are strictly
  -- more expressive
  infinite-can : Δ I.⊢ᵣ Bool
  infinite-can = r-simp (there (here refl)) p
    where
      p : Δ I.⊢ Bool ↓ tc 0
      p = i-simp (tc 0)

module Infinite⊆Ambiguous where

  open import Implicits.Resolution.Ambiguous.Resolution as A
  open import Implicits.Resolution.Infinite.Resolution as I
  open import Implicits.Syntax
  open import Implicits.Substitutions

  sound : ∀ {ν} {a : Type ν} {Δ : ICtx ν} → Δ I.⊢ᵣ a → Δ A.⊢ᵣ a
  sound (r-simp x p) = lem p (r-ivar x)
    where
      lem : ∀ {ν} {Δ : ICtx ν} {a τ} → Δ I.⊢ a ↓ τ → Δ A.⊢ᵣ a → Δ A.⊢ᵣ (simpl τ)
      lem (i-simp τ) ⊢y = ⊢y
      lem (i-iabs ⊢a b↓τ) ⊢b = lem b↓τ (r-iapp ⊢b (sound ⊢a))
      lem (i-tabs b a) ⊢y = lem a (r-tapp b ⊢y)
  sound (r-iabs p) = r-iabs (sound p)
  sound (r-tabs p) = r-tabs (sound p)

module Infinite⊂Ambiguous where
  -- but interestingly, we CANNOT use this identity, and use it to derive everything else
  -- Because we can only derive (polymorphic) rule-types from an empty context.
  -- counter-example₁ : ¬ List.[] I.⊢ᵣ simpl (tvar {suc zero} zero)
  -- counter-example₁ (r-simp () _)
