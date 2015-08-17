module Implicits.Syntactical.Substitutions where

open import Prelude hiding (lift)
open import Implicits.Syntactical.Types
open import Implicits.Syntactical.Terms
open import Implicits.Syntactical.Contexts
open import Data.Fin.Substitution
open import Data.Star hiding (map)

module TypeSubst where
  module TypeApp {T} (l : Lift T Type) where
    open Lift l hiding (var)

    infixl 5 _/_
    _/_ : ∀ {m n} → Type m → Sub T m n → Type n
    tvar x   / σ = lift (lookup x σ)
    (a →' b) / σ = (a / σ) →' (b / σ)
    ∀' x / s = ∀' (x / (s ↑))

    open Application (record { _/_ = _/_ }) using (_/✶_)

    →'-/✶-↑✶ : ∀ k {m n a b} (ρs : Subs T m n) →
               (a →' b) /✶ ρs ↑✶ k ≡ (a /✶ ρs ↑✶ k) →' (b /✶ ρs ↑✶ k)
    →'-/✶-↑✶ k ε        = refl
    →'-/✶-↑✶ k (r ◅ ρs) = cong₂ _/_ (→'-/✶-↑✶ k ρs) refl

    ∀'-/✶-↑✶ : ∀ k {m n a} (ρs : Subs T m n) →
               (∀' a) /✶ ρs ↑✶ k ≡ ∀' (a /✶ ρs ↑✶ (suc k))
    ∀'-/✶-↑✶ k ε = refl
    ∀'-/✶-↑✶ k (x ◅ ρs) = cong₂ _/_ (∀'-/✶-↑✶ k ρs) refl

  typeSubst : TermSubst Type
  typeSubst = record { var = tvar; app = TypeApp._/_ }


  open TermSubst typeSubst public hiding (var)

  infix 8 _[/_]

  -- Shorthand for single-variable type substitutions
  _[/_] : ∀ {n} → Type (suc n) → Type n → Type n
  a [/ b ] = a / sub b

  -- lifted to IsFunction instances
  _f/_ : ∀ {ν μ} {a : Type ν} → IsFunction a → (s : Sub Type ν μ) → IsFunction (a / s) 
  lambda a b f/ s = lambda (a / s) (b / s)
  ∀'-lambda f f/ s = ∀'-lambda (f f/ (s ↑))

  -- lifted to implicits
  _i/_ : ∀ {ν μ} → Implicit ν → Sub Type ν μ → Implicit μ
  rule a i/ s = rule (a f/ s)
  val b i/ s = val (b / s)

  -- shorthand for type application
  _∙_ : ∀ {ν} → (a : Type ν) → {is∀ : is-∀' a} → Type ν → Type ν
  _∙_ (∀' x) b = x [/ b ]
  _∙_ (tvar n) {is∀ = ()} _
  _∙_ (_ →' _) {is∀ = ()} _

module TermTypeSubst where

  module TermTypeApp {T} (l : Lift T Type) where
    open Lift l hiding (var)
    open TypeSubst.TypeApp l renaming (_/_ to _/tp_)

    infixl 8 _/_

    mutual 
      -- substitution implicit terms
      _it/_ : ∀ {ν μ n} → ImplicitTerm ν n → Sub T ν μ → ImplicitTerm μ n
      val x it/ s = val (x / s) 
      rule x it/ s = rule (x / s)

      -- Apply a type substitution to a term
      _/_ : ∀ {ν μ n} → Term ν n → Sub T ν μ → Term μ n
      var x      / σ = var x
      Λ t        / σ = Λ (t / σ ↑)
      λ' a t     / σ = λ' (a /tp σ) (t / σ)
      t [ a ]    / σ = (t / σ) [ a /tp σ ]
      s · t      / σ = (s / σ) · (t / σ)
      t ⟨⟩       / σ = (t / σ) ⟨⟩
      implicit e in' e' / σ = implicit (e it/ σ) in' (e' / σ)
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
  Γ / σ = map (λ s → s TypeSubst./ σ) Γ

  ctx-weaken : ∀ {ν n} → Ctx ν n → Ctx (suc ν) n
  ctx-weaken Γ = Γ / TypeSubst.wk

  weaken : ∀ {ν n} → Ktx ν n → Ktx (suc ν) n
  weaken (Γ , Δ) = (
    ctx-weaken Γ ,
    List.map (λ t → t TypeSubst.i/ TypeSubst.wk) Δ)

open TypeSubst public using (_∙_; _i/_; _f/_)
  renaming (_/_ to _tp/tp_; _[/_] to _tp[/tp_]; weaken to tp-weaken)
open TermTypeSubst public using ()
  renaming (_/_ to _tm/tp_; _[/_] to _tm[/tp_]; weaken to tm-weaken)
open KtxSubst public
  renaming (_/_ to _ctx-/_; weaken to ktx-weaken)
