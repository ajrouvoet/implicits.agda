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
open import Implicits.Improved.Infinite.Algorithm TC _tc≟_
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
  r = run_for_steps (resolve Δ Int) 10

  p : isNow r ≡ true
  p = refl

module Ex₂ where

  Δ : ICtx zero
  Δ = Bool ∷ (Bool ⇒ Int) ∷ []

  -- resolves using implicit application
  r = run_for_steps (resolve Δ Int) 10

  p : r resolved? ≡ true
  p = refl

module Ex₃ where

  Δ : ICtx zero
  Δ = Bool ∷ (∀' (Bool ⇒ (simpl (tvar zero)))) ∷ []

  -- resolves using polymorphic appliation + implicit application
  r = run_for_steps (resolve Δ Int) 10

  p : r resolved? ≡ true
  p = refl

module Ex₄ where

  Δ : ICtx zero
  Δ = Bool ∷ (∀' ((simpl (tvar zero)) ⇒ Int)) ∷ []

  r = run_for_steps (resolve Δ Int) 10

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

  r = run_for_steps (resolve Δ Int) 10

  p : r resolved? ≡ true
  p = refl

module Ex₆ where

  Δ : ICtx zero
  Δ = Bool ∷ (∀' (Bool ⇒ (simpl (tvar zero)))) ∷ []

  -- resolves rule types
  r = run_for_steps (resolve Δ (Bool ⇒ Int)) 10

  p : r resolved? ≡ true
  p = refl

module Ex₇ where

  Δ : ICtx zero
  Δ = Bool ∷ (∀' (Bool ⇒ (simpl (tvar zero)))) ∷ []

  q : Type zero
  q = (∀' (Bool ⇒ (simpl (tvar zero))))

  -- Resolves polymorphic types.
  -- Note that it doesn't resolve to the rule in the context directly.
  -- Instead, it will apply r-tabs and r-iabs, to obtain resolve Δ' ⊢ᵣ (∀' (tvar zero))
  r = run_for_steps (resolve Δ q) 10

  p : r resolved? ≡ true
  p = refl

module Ex₈ where

  Δ : ICtx zero
  Δ = Bool ∷ (∀' ((simpl (tvar zero)) ⇒ (simpl (tvar zero)))) ∷ []

  -- infinite derivation exists: not decidable
  r = run_for_steps (resolve Δ Int) 10

  p : r resolved? ≡ false
  p = refl

  ¬p : r failed? ≡ false
  ¬p = refl

module Ex₉ where

  Δ : ICtx zero
  Δ = (∀' ((Int ⇒ simpl (tvar zero)) ⇒ ((simpl (tvar zero)) ⇒ Int))) ∷ (Int ⇒ Bool) ∷ []

  r = run_for_steps (resolve Δ (Bool ⇒ Int)) 10

  p : r resolved? ≡ false
  p = refl

  ¬p : r failed? ≡ true
  ¬p = refl

  -- Below p' demonstrates however that a derivation exists!
  -- The algorithm doesn't find it because we left the ⊢unamb predicate from oliveira implicit.
  -- at some point the algorithm has to match ((simpl (mvar zero) ⇒ Int)) with Int.
  -- However, when we match the codomain Int with the goal Int (note the open mvar):
  test : mgu {m = suc zero} {ν = zero} (to-meta Int) (tc tc-int) ≡ nothing
  test = refl
  -- Because mgu requires that all meta variables are instantiated by unification
  -- and in this example (mvar zero) does not occur and thus can't be unified.

  open import Implicits.Improved.Infinite.Resolution TC _tc≟_
  open import Coinduction

  p' : Δ ⊢ᵣ (Bool ⇒ Int)
  p' = r-iabs
    (r-simp
      (there (here refl))
      (i-tabs
        (simpl (tc tc-bool))
        (i-iabs
          (♯ (r-iabs (r-simp (there (here refl)) (i-simp (tc tc-bool)))))
          (i-iabs (♯ (r-simp (here refl) (i-simp (tc tc-bool)))) (i-simp (tc tc-int)))
        )
      )
    )
