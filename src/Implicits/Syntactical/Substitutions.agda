module Implicits.Syntactical.Substitutions where

open import Prelude hiding (lift)
open import Implicits.Syntactical.Types
open import Implicits.Syntactical.Terms
open import Implicits.Syntactical.Contexts
open import Data.Fin.Substitution
open import Data.Star hiding (map)
  
open import Implicits.Syntactical.Substitutions.Types public

module TermTypeSubst where

  module TermTypeApp {T} (l : Lift T Type) where
    open Lift l hiding (var)
    open TypeSubst.TypeApp l renaming (_/_ to _tp/_)
    open PTypeSubst.MonoTypeApp l renaming (_/_ to _pt/_)

    infixl 8 _/_

    -- Apply a type substitution to a term
    _/_ : ∀ {ν μ n} → Term ν n → Sub T ν μ → Term μ n
    var x      / σ = var x
    Λ t        / σ = Λ (t / σ ↑)
    λ' a t     / σ = λ' (a tp/ σ) (t / σ)
    t [ a ]    / σ = (t / σ) [ a tp/ σ ]
    s · t      / σ = (s / σ) · (t / σ)
    t ⟨⟩       / σ = (t / σ) ⟨⟩
    let' e in' e' / σ = let' (e / σ) in' (e' / σ)
    implicit e in' e' / σ = implicit (e / σ) in' (e' / σ)
    implicit a ⇒ e in' e' / σ = implicit (a pt/ σ) ⇒ (e / σ) in' (e' / σ)

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

module BindingSubst where
  _/_ : ∀ {ν μ} → Binding ν → Sub Type ν μ → Binding μ
  _/_  (rule a b) σ = rule (a PTypeSubst./tp σ) (b PTypeSubst./tp σ)
  _/_ (val a) σ = val (a PTypeSubst./tp σ)

  weaken : ∀ {ν} → Binding ν → Binding (suc ν)
  weaken K = K / TypeSubst.wk

module KtxSubst where
  _/_ : ∀ {ν μ n} → Ktx ν n → Sub Type ν μ → Ktx μ n
  _/_ {ν} {μ} (Γ , Δ) σ = map (flip PTypeSubst._/tp_ σ) Γ , List.map (flip BindingSubst._/_ σ) Δ
  
  weaken : ∀ {ν n} → Ktx ν n → Ktx (suc ν) n
  weaken K = K / TypeSubst.wk

open TermTypeSubst public using () 
  renaming (_/_ to _tm/tp_; _[/_] to _tm[/tp_]; weaken to tm-weaken)
open BindingSubst public 
  renaming (_/_ to _binding/_; weaken to binding-weaken)
open KtxSubst public 
  renaming (_/_ to _ctx/_; weaken to ktx-weaken)
