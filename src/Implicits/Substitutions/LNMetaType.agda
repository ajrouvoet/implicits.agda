open import Prelude hiding (lift; Fin′; subst; id)

module Implicits.Substitutions.LNMetaType where

open import Implicits.Syntax.LNMetaType
open import Data.Fin.Substitution
open import Data.Star as Star hiding (map)
open import Data.Star.Properties

module MetaTypeApp {T} (l : Lift T MetaType) where
  open Lift l hiding (var)

  infixl 8 _/_

  mutual 
    _simple/_ : ∀ {m n} → MetaSType m → Sub T m n → MetaType n
    tc c simple/ σ = simpl (tc c)
    tvar x simple/ σ = simpl (tvar x)
    mvar x simple/ σ = lift $ lookup x σ
    (a →' b) simple/ σ = simpl ((a / σ) →' (b / σ))

    _/_ : ∀ {m n} → MetaType m → Sub T m n → MetaType n
    (simpl c) / σ = (c simple/ σ)
    (a ⇒ b)  / σ = (a / σ) ⇒ (b / σ)
    (∀' a)   / σ = ∀' (a / σ)

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

  tvar-/✶-↑✶ : ∀ k {c m n} (ρs : Subs T m n) →
             (simpl (tvar c)) /✶ ρs ↑✶ k ≡ simpl (tvar c)
  tvar-/✶-↑✶ k ε        = refl
  tvar-/✶-↑✶ k (r ◅ ρs) = cong₂ _/_ (tvar-/✶-↑✶ k ρs) refl 

  ∀'-/✶-↑✶ : ∀ k {m n a} (ρs : Subs T m n) →
             (∀' a) /✶ ρs ↑✶ k ≡ ∀' (a /✶ ρs ↑✶ k)
  ∀'-/✶-↑✶ k ε = refl
  ∀'-/✶-↑✶ k (x ◅ ρs) = cong₂ _/_ (∀'-/✶-↑✶ k ρs) refl

typeSubst : TermSubst MetaType
typeSubst = record { var = (λ n → simpl (mvar n)); app = MetaTypeApp._/_ }

open TermSubst typeSubst public hiding (var)
open MetaTypeApp termLift public using (_simple/_)
open MetaTypeApp varLift public using () renaming (_simple/_ to _simple/Var_)

infix 8 _[/_]

-- Shorthand for single-variable type substitutions
_[/_] : ∀ {n} → MetaType (suc n) → MetaType n → MetaType n
a [/ b ] = a / sub b

_◁m₁ : ∀ {m} (r : MetaType m) → ℕ
_◁m₁ (a ⇒ b) = b ◁m₁ 
_◁m₁ (∀' r) = 1 N+ r ◁m₁ 
_◁m₁ (simpl x) = zero

-- heads of metatypes
_◁m : ∀ {m} (r : MetaType m) → (MetaType ((r ◁m₁) N+ m))
(a ⇒ b) ◁m = b ◁m
∀' r ◁m = open-meta zero (r ◁m)
simpl x ◁m = simpl x
