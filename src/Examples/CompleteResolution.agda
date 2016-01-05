open import Prelude hiding (id; Bool; _∷_; [])

module Examples.CompleteResolution where

data TC : Set where
  tc-int : TC
  tc-bool : TC

_tc≟_ : (a b : TC) → Dec (a ≡ b)
tc-int tc≟ tc-int = yes refl
tc-int tc≟ tc-bool = no (λ ())
tc-bool tc≟ tc-int = no (λ ())
tc-bool tc≟ tc-bool = yes refl

open import Implicits.Syntax TC _tc≟_
open import Implicits.WellTyped TC _tc≟_
open import Implicits.Substitutions TC _tc≟_
open import Implicits.Syntax.Type.Unification TC _tc≟_
open import Implicits.Resolution.Finite.Resolution TC _tc≟_
open import Implicits.Resolution.Finite.Algorithm TC _tc≟_
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
  r = resolve Δ Int

  p : is-just r ≡ true
  p = refl

module Ex₂ where

  Δ : ICtx zero
  Δ = Bool ∷ (Bool ⇒ Int) ∷ []

  -- resolves using implicit application
  r = resolve Δ Int

  p : is-just r ≡ true
  p = refl

module Ex₃ where

  Δ : ICtx zero
  Δ = Bool ∷ (∀' (Bool ⇒ (simpl (tvar zero)))) ∷ []

  -- resolves using polymorphic implicit application
  r = resolve Δ Int

  p : is-just r ≡ true
  p = refl

module Ex₅ where

  -- The following context would not resolved Int in Oliveira's deterministic calculus.
  -- Demonstratint that partial resolution is more powerful for terminating contexts.
  Δ : ICtx zero
  Δ = (Bool ⇒ Int) ∷ Int ∷ []

  r = resolve Δ Int

  p : is-just r ≡ true
  p = refl

module Ex₆ where

  Δ : ICtx zero
  Δ = Bool ∷ (∀' (Bool ⇒ (simpl (tvar zero)))) ∷ []

  -- resolves rule types
  r = resolve Δ (Bool ⇒ Int)

  p : is-just r ≡ true
  p = refl

module Ex₇ where

  Δ : ICtx zero
  Δ = Bool ∷ (∀' (Bool ⇒ (simpl (tvar zero)))) ∷ []

  q : Type zero
  q = (∀' (Bool ⇒ (simpl (tvar zero))))

  -- Resolves polymorphic types.
  -- Note that it doesn't resolve to the rule in the context directly.
  -- Instead, it will apply r-tabs and r-iabs, to obtain resolve Δ' ⊢ᵣ (∀' (tvar zero))
  r = resolve Δ q

  p : is-just r ≡ true
  p = refl

module Ex₈ where

  Δ : ICtx zero
  Δ = Bool ∷ (∀' ((simpl (tvar zero)) ⇒ (simpl (tvar zero)))) ∷ []

  -- infinite derivation exists: fails divergence checking
  r = resolve Δ Int

  p : is-just r ≡ false
  p = refl

module Ex₉ where

  a⇒consta : Type zero
  a⇒consta = (∀' ((simpl (tvar zero)) ⇒ (∀' (simpl (simpl (tvar zero) →' (simpl (tvar (suc zero))))))))

  Δ : ICtx zero
  Δ = Bool ∷ a⇒consta ∷ []

  const-bool : Type zero
  const-bool = (∀' (simpl ((simpl (tvar zero)) →' Bool)))

  r = resolve Δ const-bool

  p : is-just r ≡ true
  p = refl

module Ex₁₀ where

  -- similar to Ex₉ but for this particular example we have that for the rule part
  -- || ρ₁ || ≮ || ρ₂ || such that Oliveira's ⊢term predicate on ρ₁ ⇒ ρ₂ fails
  a⇒∀a : Type zero
  a⇒∀a = (∀' ((simpl (tvar zero)) ⇒ (∀' (simpl (tvar (suc zero))))))

  Δ : ICtx zero
  Δ = Bool ∷ a⇒∀a ∷ []

  r = resolve Δ (∀' Bool)

  p : is-just r ≡ true
  p = refl
