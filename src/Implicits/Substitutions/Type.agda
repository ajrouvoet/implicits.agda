open import Prelude hiding (lift; Fin′; subst; id)

module Implicits.Substitutions.Type (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Implicits.Syntax.Type TC _tc≟_
open import Data.Fin.Substitution
open import Data.Star as Star hiding (map)
open import Data.Star.Properties

module TypeApp {T} (l : Lift T Type) where
  open Lift l hiding (var)

  infixl 8 _/_

  mutual 
    _simple/_ : ∀ {m n} → SimpleType m → Sub T m n → Type n
    tc c simple/ σ = simpl (tc c)
    tvar x simple/ σ = lift (lookup x σ)
    (a →' b) simple/ σ = simpl ((a / σ) →' (b / σ))

    _/_ : ∀ {m n} → Type m → Sub T m n → Type n
    (simpl c) / σ = (c simple/ σ)
    (a ⇒ b)  / σ = (a / σ) ⇒ (b / σ)
    (∀' a)   / σ = ∀' (a / σ ↑)

  open Application (record { _/_ = _/_ }) using (_/✶_)

  →'-/✶-↑✶ : ∀ k {m n a b} (ρs : Subs T m n) →
             (simpl (a →' b)) /✶ ρs ↑✶ k ≡ simpl ((a /✶ ρs ↑✶ k) →' (b /✶ ρs ↑✶ k))
  →'-/✶-↑✶ k ε        = refl
  →'-/✶-↑✶ k (r ◅ ρs) = cong₂ _/_ (→'-/✶-↑✶ k ρs) refl

  ⇒-/✶-↑✶ : ∀ k {m n a b} (ρs : Subs T m n) →
             (a ⇒ b) /✶ ρs ↑✶ k ≡ (a /✶ ρs ↑✶ k) ⇒ (b /✶ ρs ↑✶ k)
  ⇒-/✶-↑✶ k ε        = refl
  ⇒-/✶-↑✶ k (r ◅ ρs) = cong₂ _/_ (⇒-/✶-↑✶ k ρs) refl

  tc-/✶-↑✶ : ∀ k {c m n} (ρs : Subs T m n) →
             (simpl (tc c)) /✶ ρs ↑✶ k ≡ simpl (tc c)
  tc-/✶-↑✶ k ε        = refl
  tc-/✶-↑✶ k (r ◅ ρs) = cong₂ _/_ (tc-/✶-↑✶ k ρs) refl 

  ∀'-/✶-↑✶ : ∀ k {m n a} (ρs : Subs T m n) →
             (∀' a) /✶ ρs ↑✶ k ≡ ∀' (a /✶ ρs ↑✶ (suc k))
  ∀'-/✶-↑✶ k ε = refl
  ∀'-/✶-↑✶ k (x ◅ ρs) = cong₂ _/_ (∀'-/✶-↑✶ k ρs) refl

typeSubst : TermSubst Type
typeSubst = record { var = (λ n → simpl (tvar n)); app = TypeApp._/_ }

open TermSubst typeSubst public hiding (var)
open TypeApp termLift public using (_simple/_)
open TypeApp varLift public using () renaming (_simple/_ to _simple/Var_)

infix 8 _[/_]

-- Shorthand for single-variable type substitutions
_[/_] : ∀ {n} → Type (suc n) → Type n → Type n
a [/ b ] = a / sub b

-- shorthand for type application
infixl 8 _∙_
_∙_ : ∀ {ν} → (a : Type ν) → {is∀ : is-∀' a} → Type ν → Type ν
_∙_ (simpl (tvar n)) {is∀ = ()} _
_∙_ (simpl (tc c)) b = simpl (tc c)
_∙_ (simpl (_ →' _)) {is∀ = ()} _
_∙_ (∀' x) b = x [/ b ]
_∙_ (_ ⇒ _) {is∀ = ()} _

stp-weaken : ∀ {ν} → SimpleType ν → SimpleType (suc ν)
stp-weaken (tc x) = tc x
stp-weaken (tvar n) = tvar (suc n)
stp-weaken (a →' b) = weaken a →' weaken b
