open import Prelude

module Implicits.Improved.Finite.Resolution (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Coinduction
open import Data.Fin.Substitution
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Induction
open import Induction.Nat
open import Implicits.Improved.Finite.Termination.Stack TC _tc≟_

infixl 5 _⊢ᵣ_
infixl 5 _&_⊢ᵣ_ _&_,_⊢_↓_

mutual

  -- Δ & s , r ⊢ a ↓ τ denotes:
  -- Under the context Δ, with stack of resolution goals s, the type a yields simple type τ.
  -- 'r' is used to keep track of the rule from the context that yielded 'a'
  -- ('a' is getting recursively refined)
  data _&_,_⊢_↓_ {ν} (Δ : ICtx ν) :
    ∀ {r} → Stack Δ → r List.∈ Δ → Type ν → SimpleType ν → Set where

    i-simp : ∀ {r s} {r∈Δ : r List.∈ Δ} a → Δ & s , r∈Δ ⊢ simpl a ↓ a
    i-iabs : ∀ {ρ₁ ρ₂ a r s} {r∈Δ : r List.∈ Δ} →
             ρ₁ for r∈Δ ⊬dom s → -- subproblems decrease when recursing
             Δ & (s push ρ₁ for r∈Δ) ⊢ᵣ ρ₁ → -- domain is resolvable
             Δ & s , r∈Δ ⊢ ρ₂ ↓ a → -- codomain matches
             Δ & s , r∈Δ ⊢ ρ₁ ⇒ ρ₂ ↓ a
    i-tabs : ∀ {ρ a r s} {r∈Δ : r List.∈ Δ} b →
             Δ & s , r∈Δ ⊢ ρ tp[/tp b ] ↓ a → Δ & s , r∈Δ ⊢ ∀' ρ ↓ a

  data _&_⊢ᵣ_ {ν} (Δ : ICtx ν) : Stack Δ → Type ν → Set where
    r-simp : ∀ {r τ s} → (r∈Δ : r List.∈ Δ) → Δ & s , r∈Δ ⊢ r ↓ τ → Δ & s ⊢ᵣ simpl τ
    r-iabs : ∀ {ρ₁ ρ₂} {s : Stack Δ} → ((ρ₁ List.∷ Δ) & (s prepend ρ₁) ⊢ᵣ ρ₂) →
             Δ & s ⊢ᵣ (ρ₁ ⇒ ρ₂)
    r-tabs : ∀ {ρ s} → ictx-weaken Δ & stack-weaken s ⊢ᵣ ρ → Δ & s ⊢ᵣ ∀' ρ

-- TODO: This doesn't hold.
-- e.g. we can unify (a → b) with the codomain of a rule (a → b → a) ⇒ (a → b)
-- so the subgoal is larger than the initial goal.
--
-- We instantiate the stack with types that act as 'infinity' on the goal.
-- Every possible 'subgoal' we encounter and push to the stack will certainly
-- be smaller than r
_⊢ᵣ_ : ∀ {ν} → ICtx ν → Type ν → Set
Δ ⊢ᵣ r = Δ & All.tabulate (const r) ⊢ᵣ r
