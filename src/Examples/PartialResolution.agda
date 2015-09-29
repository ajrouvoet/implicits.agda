open import Prelude hiding (id; Bool; _∷_; [])

module Examples.PartialResolution where

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
open import Implicits.Improved.Ambiguous.PartialResolution TC _tc≟_
open import Data.Maybe
open import Data.List
open import Category.Monad.Partiality

Bool : ∀ {n} → Type n
Bool = simpl (tc tc-bool)

Int : ∀ {n} → Type n
Int = simpl (tc tc-int)

module Ex₁ where

  Δ : ICtx zero
  Δ = Bool ∷ Int ∷ []

  -- resolves directly using a value from the implicit context
  r = run_for_steps (resolve Δ Int) 100

  p : isNow r ≡ true
  p = refl

module Ex₂ where

  Δ : ICtx zero
  Δ = Bool ∷ (Bool ⇒ Int) ∷ []

  -- resolves using implicit application
  r = run_for_steps (resolve Δ Int) 100

  p : r resolved? ≡ true
  p = refl

module Ex₃ where

  Δ : ICtx zero
  Δ = Bool ∷ (∀' (Bool ⇒ (simpl (tvar zero)))) ∷ []

  -- resolves using polymorphic appliation + implicit application
  r = run_for_steps (resolve Δ Int) 100

  p : r resolved? ≡ true
  p = refl

module Ex₄ where

  Δ : ICtx zero
  Δ = Bool ∷ (∀' ((simpl (tvar zero)) ⇒ Int)) ∷ []

  r = run_for_steps (resolve Δ Int) 100

  -- Maybe surprisingly this fails.
  -- But we should note that unification on the codomain of the rule does not fix the domain to a
  -- concrete type, such that it's instantiation is left ambiguous.
  -- Like Oliveira we reject those rules, because they lead to ambiguous terms.
  p : r failed? ≡ true
  p = refl

module Ex₅ where

  -- The following context would not resolved Int in Oliveira's deterministic calculus.
  -- Demonstratint that partial resolution is more powerful for terminating contexts.
  Δ : ICtx zero
  Δ = (Bool ⇒ Int) ∷ Int ∷ []

  r = run_for_steps (resolve Δ Int) 100

  p : r resolved? ≡ true
  p = refl

module Ex₆ where

  Δ : ICtx zero
  Δ = Bool ∷ (∀' (Bool ⇒ (simpl (tvar zero)))) ∷ []

  -- resolves rule types
  r = run_for_steps (resolve Δ (Bool ⇒ Int)) 100

  p : r resolved? ≡ true
  p = refl

module Ex₇ where

  Δ : ICtx zero
  Δ = Bool ∷ (∀' (Bool ⇒ (simpl (tvar zero)))) ∷ []

  -- Resolves polymorphic types.
  -- Note that it doesn't resolve to the rule in the context directly.
  -- Instead, it will apply r-tabs and r-iabs, to obtain resolve Δ' ⊢ᵣ (∀' (tvar zero))
  r = run_for_steps (resolve Δ (∀' (Bool ⇒ (simpl (tvar zero))))) 100

  p : r resolved? ≡ true
  p = refl
