module Examples.DivergingContext where

open import Prelude

data TC : Set where
  tc-int : TC
  tc-bool : TC

_tc≟_ : (a b : TC) → Dec (a ≡ b)
tc-int tc≟ tc-int = yes refl
tc-int tc≟ tc-bool = no (λ ())
tc-bool tc≟ tc-int = no (λ ())
tc-bool tc≟ tc-bool = yes refl

open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.WellTyped TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.Types.Unification TC _tc≟_
open import Implicits.Improved.Infinite.Resolution TC _tc≟_
open import Data.Maybe
open import Data.List
open import Coinduction
open import Data.List.Any.Membership using (map-mono)
open import Data.List.Any
open Membership-≡

Int : ∀ {ν} → Type ν
Int = simpl (tc tc-int)

module Ex₁ where

  r : Type zero
  r = (∀' (((simpl (x →' x)) ⇒ (simpl (x →' (simpl (x →' x))))) ⇒ x))
    where
      x = (simpl (tvar zero))
  
  Δ : ICtx zero
  Δ = r ∷ []

  -- Exploiting coinductive definition here to show that there is an infinite derivation
  -- of any type under the context Δ with the special characteristic that the context grows to
  -- infinity as well!
  --
  -- This may not be immediately obvious, but it can be seen by exploring the first argument of 'p'
  -- in the recursive calls, denoting the growing context.
  -- Also note that the element added to the context won't ever match the goal.
  -- This is not proven here, but an argument for it is made in the form of ¬r↓goal
  p : ∀ Δ' a → Δ ⊆ Δ' → Δ' ⊢ᵣ simpl a
  p Δ' a f = r-simp (f (here refl))
    (i-tabs
      (simpl a)
      (i-iabs (♯ r-iabs (p (new-r ∷ Δ') new-goal (λ x → there (f x)))) (i-simp a)))
    where
      new-r = simpl (simpl a →' simpl a)
      new-goal = (simpl a →' simpl (simpl a →' simpl a))

      ¬r↓goal : ¬ (new-r ∷ Δ') ⊢ new-r ↓ new-goal
      ¬r↓goal ()
