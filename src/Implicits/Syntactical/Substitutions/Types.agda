module Implicits.Syntactical.Substitutions.Types where

open import Prelude hiding (lift)
open import Implicits.Syntactical.Types
open import Implicits.Syntactical.Terms
open import Data.Fin.Substitution
open import Data.Star hiding (map)
  
module TypeSubst where
  module TypeApp {T} (l : Lift T Type) where
    open Lift l hiding (var)

    infixl 8 _/_

    _/_ : ∀ {m n} → Type m → Sub T m n → Type n
    tvar x   / σ = lift (lookup x σ)
    (a →' b) / σ = (a / σ) →' (b / σ)

    open Application (record { _/_ = _/_ }) using (_/✶_)

    →'-/✶-↑✶ : ∀ k {m n a b} (ρs : Subs T m n) →
               (a →' b) /✶ ρs ↑✶ k ≡ (a /✶ ρs ↑✶ k) →' (b /✶ ρs ↑✶ k)
    →'-/✶-↑✶ k ε        = refl
    →'-/✶-↑✶ k (r ◅ ρs) = cong₂ _/_ (→'-/✶-↑✶ k ρs) refl

  typeSubst : TermSubst Type
  typeSubst = record { var = tvar; app = TypeApp._/_ }


  open TermSubst typeSubst public hiding (var)

  infix 8 _[/_]

  -- Shorthand for single-variable type substitutions
  _[/_] : ∀ {n} → Type (suc n) → Type n → Type n
  a [/ b ] = a / sub b

module PTypeSubst where
  -- polytype function constructor
  -- even though the termination checker can't see it, 
  -- this must terminate: 
  -- induction is on the remaining number of ∀' constructors, which is strictly decreasing
  {-# NO_TERMINATION_CHECK #-}
  _→ₚ_ : ∀ {n} → PolyType n → PolyType n → PolyType n
  mono x →ₚ mono y = mono (x →' y)
  mono x →ₚ ∀' r = ∀' ((mono $ TypeSubst.weaken x) →ₚ r)
  ∀' l →ₚ mono r = ∀' (l →ₚ (mono $ TypeSubst.weaken r))
  ∀' l →ₚ ∀' r = ∀' (l →ₚ r)

  module TypeApp {T} (l : Lift T PolyType) where
    open Lift l hiding (var)

    infixl 8 _/_

    _/_ : ∀ {ν μ} → PolyType ν → Sub T ν μ → PolyType μ
    mono (tvar n) / σ = lift $ lookup n σ
    mono (x →' y) / σ = (mono x / σ) →ₚ (mono y / σ)
    ∀' x / σ = ∀' (x / (σ ↑))

    open Application (record { _/_ = _/_ }) using (_/✶_)

  typeSubst : TermSubst PolyType
  typeSubst = record { var = mono ∘ tvar; app = TypeApp._/_ }

  module tms = TermSubst typeSubst 

  -- lift substitution of types into polytypes
  module MonoTypeApp {T} (l : Lift T Type) where
    open Lift l hiding (var)

    infixl 6 _/_
    _/_ : ∀ {ν μ} → PolyType ν → Sub T ν μ → PolyType μ
    x / σ = x tms./ (map (mono ∘ lift) σ)
  
  open MonoTypeApp TypeSubst.termLift public renaming (_/_ to _/tp_)

  _[/tp_] : ∀ {ν} → PolyType (suc ν) → Type ν → PolyType ν
  _[/tp_] p t = p /tp TypeSubst.sub t
  
  open tms public

  -- Shorthand for single-variable type substitutions
  infix 8 _[/_]
  _[/_] : ∀ {n} → PolyType (suc n) → PolyType n → PolyType n
  a [/ b ] = a / sub b

open TypeSubst public using ()
  renaming (_/_ to _tp/tp_; _[/_] to _tp[/tp_]; weaken to tp-weaken)
open PTypeSubst public using (_→ₚ_)
  renaming (_/tp_ to _pt/tp_; _[/tp_] to _pt[/tp_]; _[/_] to _pt[/pt_]; weaken to pt-weaken)
