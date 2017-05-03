module SystemF.Substitutions.Types where

open import Prelude
open import SystemF.Syntax.Type
open import Data.Fin.Substitution
open import Data.Star hiding (map)
open import Data.Vec

module TypeSubst where
  module TypeApp {T} (l : Lift T Type) where
    open Lift l hiding (var)

    infixl 8 _/_

    _/_ : ∀ {m n} → Type m → Sub T m n → Type n
    tc c     / σ = tc c
    tvar x   / σ = lift (lookup x σ)
    (a →' b) / σ = (a / σ) →' (b / σ)
    (a ⟶ b) / σ = (a / σ) ⟶ (b / σ)
    ∀' a     / σ = ∀' (a / σ ↑)

    open Application (record { _/_ = _/_ }) using (_/✶_)

    →'-/✶-↑✶ : ∀ k {m n a b} (ρs : Subs T m n) →
               (a →' b) /✶ ρs ↑✶ k ≡ (a /✶ ρs ↑✶ k) →' (b /✶ ρs ↑✶ k)
    →'-/✶-↑✶ k ε        = refl
    →'-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _/_ (→'-/✶-↑✶ k ρs) refl


    ⟶-/✶-↑✶ : ∀ k {m n a b} (ρs : Subs T m n) →
               (a ⟶ b) /✶ ρs ↑✶ k ≡ (a /✶ ρs ↑✶ k) ⟶ (b /✶ ρs ↑✶ k)
    ⟶-/✶-↑✶ k ε        = refl
    ⟶-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _/_ (⟶-/✶-↑✶ k ρs) refl

    ∀'-/✶-↑✶ : ∀ k {m n a} (ρs : Subs T m n) →
               (∀' a) /✶ ρs ↑✶ k ≡ ∀' (a /✶ ρs ↑✶ (1 + k))
    ∀'-/✶-↑✶ k ε        = refl
    ∀'-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _/_ (∀'-/✶-↑✶ k ρs) refl

    tc-/✶-↑✶ : ∀ k {c m n} (ρs : Subs T m n) →
               (tc c) /✶ ρs ↑✶ k ≡ tc c
    tc-/✶-↑✶ k ε        = refl
    tc-/✶-↑✶ k (r ◅ ρs) = cong₂ _/_ (tc-/✶-↑✶ k ρs) refl 

  typeSubst : TermSubst Type
  typeSubst = record { var = tvar; app = TypeApp._/_ }

  open TermSubst typeSubst public hiding (var)

  infix 8 _[/_]

  -- Shorthand for single-variable type substitutions
  _[/_] : ∀ {n} → Type (suc n) → Type n → Type n
  a [/ b ] = a / sub b

open TypeSubst public using ()
  renaming (_/_ to _tp/tp_; _[/_] to _tp[/tp_]; weaken to tp-weaken)
