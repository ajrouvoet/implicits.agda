module Implicits.Calculus.Substitutions where

open import Prelude hiding (lift)
open import Implicits.Calculus.Types
open import Implicits.Calculus.Terms
open import Implicits.Calculus.Contexts
open import Data.Fin.Substitution
open import Data.Star hiding (map)

module TypeSubst where
  module TypeApp {T} (l : Lift T Type) where
    open Lift l hiding (var)

    infixl 8 _/_

    _/_ : ∀ {m n} → Type m → Sub T m n → Type n
    tvar x   / σ = lift (lookup x σ)
    (a →' b) / σ = (a / σ) →' (b / σ)
    (a ⇒ b)  / σ = (a / σ) ⇒ (b / σ)

    open Application (record { _/_ = _/_ }) using (_/✶_)

    →'-/✶-↑✶ : ∀ k {m n a b} (ρs : Subs T m n) →
               (a →' b) /✶ ρs ↑✶ k ≡ (a /✶ ρs ↑✶ k) →' (b /✶ ρs ↑✶ k)
    →'-/✶-↑✶ k ε        = refl
    →'-/✶-↑✶ k (r ◅ ρs) = cong₂ _/_ (→'-/✶-↑✶ k ρs) refl

    ⇒-/✶-↑✶ : ∀ k {m n a b} (ρs : Subs T m n) →
               (a ⇒ b) /✶ ρs ↑✶ k ≡ (a /✶ ρs ↑✶ k) ⇒ (b /✶ ρs ↑✶ k)
    ⇒-/✶-↑✶ k ε        = refl
    ⇒-/✶-↑✶ k (r ◅ ρs) = cong₂ _/_ (⇒-/✶-↑✶ k ρs) refl

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

  -- polytype rule constructor
  {-# NO_TERMINATION_CHECK #-}
  _⇒ₚ_ : ∀ {n} → PolyType n → PolyType n → PolyType n
  mono x ⇒ₚ mono y = mono (x ⇒ y)
  mono x ⇒ₚ ∀' r = ∀' ((mono $ TypeSubst.weaken x) ⇒ₚ r)
  ∀' l ⇒ₚ mono r = ∀' (l ⇒ₚ (mono $ TypeSubst.weaken r))
  ∀' l ⇒ₚ ∀' r = ∀' (l ⇒ₚ r)

  -- lift substitution of types into polytypes
  infixl 6 _/tp_
  _/tp_ : ∀ {ν μ} → PolyType ν → Sub Type ν μ → PolyType μ
  mono x /tp σ = mono $ x TypeSubst./ σ
  ∀' x /tp σ = ∀' (x /tp (σ TypeSubst.↑))
  
  _[/tp_] : ∀ {ν} → PolyType (suc ν) → Type ν → PolyType ν
  _[/tp_] p t = p /tp TypeSubst.sub t

  module TypeApp {T} (l : Lift T PolyType) where
    open Lift l hiding (var)

    infixl 8 _/_

    _/_ : ∀ {ν μ} → PolyType ν → Sub T ν μ → PolyType μ
    mono (tvar n) / σ = lift $ lookup n σ
    mono (x →' y) / σ = (mono x / σ) →ₚ (mono y / σ)
    mono (x ⇒ y) / σ = (mono x / σ) ⇒ₚ (mono y / σ)
    ∀' x / σ = ∀' (x / (σ ↑))

    open Application (record { _/_ = _/_ }) using (_/✶_)

  typeSubst : TermSubst PolyType
  typeSubst = record { var = mono ∘ tvar; app = TypeApp._/_ }

  open TermSubst typeSubst public hiding (var)

  -- Shorthand for single-variable type substitutions
  infix 8 _[/_]
  _[/_] : ∀ {n} → PolyType (suc n) → PolyType n → PolyType n
  a [/ b ] = a / sub b
  
module TermTypeSubst where

  module TermTypeApp {T} (l : Lift T Type) where
    open Lift l hiding (var)
    open TypeSubst.TypeApp l renaming (_/_ to _/tp_)

    infixl 8 _/_

    -- Apply a type substitution to a term
    _/_ : ∀ {ν μ n} → Term ν n → Sub T ν μ → Term μ n
    var x      / σ = var x
    Λ t        / σ = Λ (t / σ ↑)
    λ' a t     / σ = λ' (a /tp σ) (t / σ)
    t [ a ]    / σ = (t / σ) [ a /tp σ ]
    s · t      / σ = (s / σ) · (t / σ)
    ρ a t      / σ = ρ (a /tp σ) (t / σ)
    t ⟨⟩       / σ = (t / σ) ⟨⟩
    implicit e in' e' / σ = implicit (e / σ) in' (e' / σ)
    let' e in' e' / σ = let' (e / σ) in' (e' / σ)

  open TypeSubst using (varLift; termLift; sub)

  module Lifted {T} (lift : Lift T Type) {n} where
    application : Application (λ ν → Term ν n) T
    application = record { _/_ = TermTypeApp._/_ lift {n = n} }

    open Application application public

  open Lifted termLift public

  -- apply a type variable substitution (renaming) to a term
  _/Var_ : ∀ {ν μ n} → Term ν n → Sub Fin ν μ → Term μ n
  _/Var_ = TermTypeApp._/_ varLift

  -- weaken a term with an additional type variable
  weaken : ∀ {ν n} → Term ν n → Term (suc ν) n
  weaken t = t /Var VarSubst.wk

  infix 8 _[/_]

  -- shorthand for single-variable type substitutions in terms
  _[/_] : ∀ {ν n} → Term (suc ν) n → Type ν → Term ν n
  t [/ b ] = t / sub b

module KtxSubst where
  
  _/_ : ∀ {ν μ n} → Ctx ν n → Sub Type ν μ → Ctx μ n
  Γ / σ = map (λ s → s PTypeSubst./tp σ) Γ
  
  ctx-weaken : ∀ {ν n} → Ctx ν n → Ctx (suc ν) n
  ctx-weaken Γ = Γ / TypeSubst.wk
  
  weaken : ∀ {ν n} → Ktx ν n → Ktx (suc ν) n
  weaken (Γ , Δ) = (
    ctx-weaken Γ , 
    List.map (λ t → t PTypeSubst./tp TypeSubst.wk) Δ)

open TypeSubst public using ()
  renaming (_/_ to _tp/tp_; _[/_] to _tp[/tp_]; weaken to tp-weaken)
open PTypeSubst public using (_→ₚ_; _⇒ₚ_)
  renaming (_/tp_ to _pt/tp_; _[/tp_] to _pt[/tp_]; _[/_] to _pt[/pt_]; weaken to pt-weaken)
open TermTypeSubst public using () 
  renaming (_/_ to _tm/tp_; _[/_] to _tm[/tp_]; weaken to tm-weaken)
open KtxSubst public 
  renaming (_/_ to _ctx-/_; weaken to ktx-weaken)
