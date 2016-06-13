open import Prelude hiding (id; Bool; _∷_; [])

module Examples.Infinite where
open import Implicits.Syntax
open import Implicits.WellTyped
open import Implicits.Substitutions
open import Implicits.Syntax.Type.Unification
open import Implicits.Resolution.Infinite.Resolution
open TypingRules _⊢ᵣ_
open import Data.Maybe
open import Data.List

tc-bool = 0
tc-int = 1

Bool : ∀ {n} → Type n
Bool = simpl (tc tc-bool)

Int : ∀ {n} → Type n
Int = simpl (tc tc-int)

module Ex₁ where
  Δ : ICtx zero
  Δ = (∀' (TVar zero ⇒ TVar zero)) ∷ []

  p : Δ ⊢ᵣ (Int ⇒ Int)
  p = r-iabs (r-simp (there (here refl))
    (i-tabs
      Int
        (i-iabs (r-simp (here refl) (i-simp (tc tc-int))) (i-simp (tc tc-int)))))

module Ex₂ where

  implicitly : ∀ {ν n} → Term ν n
  implicitly = Λ (ρ α (var zero))
    where
      α = TVar zero

  Implicitly : ∀ {ν n} {K : Ktx ν n} → K ⊢ implicitly ∈ (∀' (TVar zero ⇒ TVar zero))
  Implicitly = Λ (ρ (ua-simp [] All.[]) (var zero))
