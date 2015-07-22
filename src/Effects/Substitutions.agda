module Effects.Substitutions where

open import Prelude hiding (lift)
open import Effects.Terms
open import Data.Fin.Substitution
open import Data.Star hiding (map)

module TypeTypeSubst {η : ℕ} where
  Type′ : ℕ → Set
  Type′ = flip Type η

  module TypeApp {T} (l : Lift T Type′) where
    open Lift l hiding (var)

    infixl 8 _/_

    _/_ : ∀ {m n} → Type′ m → Sub T m n → Type′ n
    void     / σ = void
    tvar x   / σ = lift (lookup x σ)
    (a →[ e ] b) / σ = (a / σ) →[ e ] (b / σ)
    (∀' a)   / σ = ∀' (a / σ ↑)

    open Application (record { _/_ = _/_ }) using (_/✶_)

    →'-/✶-↑✶ : ∀ k {m n a b e} (ρs : Subs T m n) →
               (a →[ e ] b) /✶ ρs ↑✶ k ≡ (a /✶ ρs ↑✶ k) →[ e ] (b /✶ ρs ↑✶ k)
    →'-/✶-↑✶ k ε        = refl
    →'-/✶-↑✶ k (r ◅ ρs) = cong₂ _/_ (→'-/✶-↑✶ k ρs) refl

    postulate ∀'-/✶-↑✶ : ∀ k {m n a} (ρs : Subs T m n) →
               (∀' a) /✶ ρs ↑✶ k ≡ ∀' (a /✶ ρs ↑✶ (suc k))

  typeSubst : TermSubst Type′
  typeSubst = record { var = tvar; app = TypeApp._/_ }

  open TermSubst typeSubst public hiding (var)

  infix 8 _[/_]

  -- Shorthand for single-variable type substitutions
  _[/_] : ∀ {n} → Type′ (suc n) → Type′ n → Type′ n
  a [/ b ] = a / sub b

module EffectEffectSubst where
  
  module EffectApp {T} (l : Lift T Effect) where
    open Lift l hiding (var)

    infixl 8 _/_

    _/_ : ∀ {m n} → Effect m → Sub T m n → Effect n
    evar x / s = lift $ lookup x s
    IO / s = IO
    Reads / s = Reads
    Writes / s = Writes
    Throws / s = Throws
    Pure / s = Pure
    e ∪ f / s = (e / s) ∪ (f / s)
    H e / s = H (e / s ↑)

    open Application (record { _/_ = _/_ }) using (_/✶_)

  typeSubst : TermSubst Effect
  typeSubst = record { var = evar; app = EffectApp._/_ }


  open TermSubst typeSubst public hiding (var)

  infix 8 _[/_]

  -- Shorthand for single-variable effect substitutions
  _[/_] : ∀ {n} → Effect (suc n) → Effect n → Effect n
  a [/ b ] = a / sub b

module TypeEffectSubst where
  module TypeEffectApp {T} (l : Lift T Effect) where
    open Lift l hiding (var)
    open EffectEffectSubst.EffectApp l renaming (_/_ to _/e_)

    infixl 8 _/_

    _/_ : ∀ {ν m n} → Type ν m → Sub T m n → Type ν n
    void     / σ = void
    tvar x   / σ = tvar x
    (a →[ e ] b) / σ = (a / σ) →[ e /e σ ] (b / σ)
    (∀' a)   / σ = ∀' (a / σ)
  
  open EffectEffectSubst using (varLift; termLift; sub)

  module Lifted {T} (lift : Lift T Effect) {ν} where
    application : Application (Type ν) T
    application = record { _/_ = TypeEffectApp._/_ lift {ν = ν} }

    open Application application public

  open Lifted termLift public

  infix 8 _[/_]

  -- Shorthand for single-variable type substitutions
  _[/_] : ∀ {ν η} → Type ν (suc η) → Effect η → Type ν η
  a [/ b ] = a / sub b

  weaken : ∀ {ν η} → Type ν η → Type ν (suc η)
  weaken a = a / EffectEffectSubst.wk

module ContextTypeSubst where

  infixl 8 _/_
  _/_ : ∀ {ν η μ n} → Ctx ν η n → Sub (flip Type η) ν μ → Ctx μ η n
  c / s = map (flip TypeTypeSubst._/_ s) c

  weaken : ∀ {ν η n} → Ctx ν η n → Ctx (suc ν) η n
  weaken c = c / TypeTypeSubst.wk

module ContextEffectSubst where

  infixl 8 _/_
  _/_ : ∀ {ν η φ n} → Ctx ν η n → Sub Effect η φ → Ctx ν φ n
  c / s = map (flip TypeEffectSubst._/_ s) c

  weaken : ∀ {ν η n} → Ctx ν η n → Ctx ν (suc η) n
  weaken c = c / EffectEffectSubst.wk

open TypeTypeSubst public using ()
  renaming (_/_ to _/tp_; weaken to tp-weaken; _[/_] to _[/tp_])
open TypeEffectSubst public using ()
  renaming (_/_ to _tp/ef_; weaken to tp-ef-weaken)
open EffectEffectSubst public using ()
  renaming (_/_ to _/ef_; weaken to ef-weaken; _[/_] to _[/ef_])
open ContextTypeSubst public using ()
  renaming (_/_ to _ctx/tp_; weaken to ctx-tp-weaken)
open ContextEffectSubst public using ()
  renaming (_/_ to _ctx/ef_; weaken to ctx-ef-weaken)
