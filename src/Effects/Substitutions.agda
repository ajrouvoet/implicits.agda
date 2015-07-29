open import Prelude hiding (lift; Fin′; subst)

module Effects.Substitutions (EC : Set) (_ec≟_ : Decidable {A = EC} _≡_ ) where

open import Effects.Terms EC _ec≟_
open import Data.Fin.Substitution
open import Data.Star hiding (map)

module EffectEffectSubst where
  
  module EffectApp {T} (l : Lift T Effect) where
    open Lift l hiding (var)

    infixl 8 _/_

    _/_ : ∀ {m n} → Effect m → Sub T m n → Effect n
    evar x / s = lift $ lookup x s
    has c / s = has c
    H e / s = H (e / s ↑)

    _/s_ : ∀ {m n} → Effects m → Sub T m n → Effects n
    e /s s = List.map (flip _/_ s) e

    open Application (record { _/_ = _/_ }) using (_/✶_)

  effSubst : TermSubst Effect
  effSubst = record { var = evar; app = EffectApp._/_ }

  open TermSubst effSubst public hiding (var) renaming (_/_ to _/e_)

  _/_ = EffectApp._/s_ termLift

  -- Shorthand for single-variable effect substitutions
  infix 8 _[/_]
  _[/_] : ∀ {n} → Effects (suc n) → Effect n → Effects n
  a [/ b ] = a / (sub b)

module EffectsEffectsSubst where
  
  module EffectsApp {T} (l : Lift T Effects) where
    open Lift l hiding (var)

    _/e_ : ∀ {m n} → Effect m → Sub T m n → Effects n
    evar x /e as = lift $ lookup x as
    has x /e as = List.[ has x ]
    H e /e as = H' (e /e (as ↑))

    infixl 8 _/_
    _/_ : ∀ {m n} → Effects m → Sub T m n → Effects n
    es / as = List.concat (List.map (flip _/e_ as) es)

  effsSubst : TermSubst Effects
  effsSubst = record { var = (λ n → List.[ evar n ]); app = EffectsApp._/_ }

  open TermSubst effsSubst public

  -- Shorthand for single-variable effect substitutions
  infix 8 _[/_]
  _[/_] : ∀ {n} → Effects (suc n) → Effects n → Effects n
  a [/ b ] = a / (sub b)

module TypeEffectSubst where
  module TypeEffectApp {T} (l : Lift T Effect) where
    open Lift l hiding (var)
    open EffectEffectSubst.EffectApp l renaming (_/_ to _/e_)

    infixl 8 _/_

    _/_ : ∀ {ν m n} → Type ν m → Sub T m n → Type ν n
    unit     / σ = unit
    tvar x   / σ = tvar x
    (a →[ e ] b) / σ = (a / σ) →[ e /s σ ] (b / σ)
    (∀' a)   / σ = ∀' (a / σ)
    (H a)    / σ = H (a / σ ↑)
  
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

module TypeTypeSubst where
  -- substitution that takes a Type ν η to a Type ν μ
  TypeSub : (ℕ → ℕ → Set) → ℕ → ℕ → ℕ → Set
  TypeSub T ν η μ = Sub (flip T η) ν μ

  record TypeLift (T : ℕ → ℕ → Set) : Set where
    infix 10 _↑ef _↑tp
    field
      lift : ∀ {ν η} → T ν η → Type ν η
      _↑tp : ∀ {ν η μ} → TypeSub T ν η μ → TypeSub T (suc ν) η (suc μ)
      _↑ef : ∀ {ν η μ} → TypeSub T ν η μ → TypeSub T ν (suc η) μ
  
  module TypeApp {T} (l : TypeLift T) where
    open TypeLift l

    infixl 8 _/_

    _/_ : ∀ {ν η μ} → Type ν η → TypeSub T ν η μ → Type μ η
    unit     / σ = unit
    tvar x   / σ = lift (lookup x σ)
    (a →[ e ] b) / σ = (a / σ) →[ e ] (b / σ)
    (∀' a)   / σ = ∀' (a / σ ↑tp)
    (H a)    / σ = H (a / σ ↑ef) 

  Fin′ : ℕ → ℕ → Set
  Fin′ n _ = Fin n

  varLift : TypeLift Fin′
  varLift = record { lift = tvar; _↑tp = VarSubst._↑; _↑ef = id }

  infixl 8 _/Var_

  _/Var_ : ∀ {m n k} → Type m n → Sub Fin m k → Type k n
  _/Var_ = TypeApp._/_ varLift

  private
    module ExpandSimple {η : ℕ} where
      simple : Simple (flip Type η)
      simple = record { var = tvar; weaken = λ t → t /Var VarSubst.wk }

      open Simple simple public

  open ExpandSimple  using (_↑; simple)

  termLift : TypeLift Type
  termLift = record
    { lift = id; _↑tp = _↑ ; _↑ef = λ ρ → map TypeEffectSubst.weaken ρ }

  private
    module ExpandSubst {η : ℕ} where
      app : Application (flip Type η) (flip Type η)
      app = record { _/_ = TypeApp._/_ termLift {η = η} }

      subst : Subst (flip Type η)
      subst = record
        { simple      = simple
        ; application = app
        }

      open Subst subst public

  open ExpandSubst public hiding (var; simple)

  infix 8 _[/_]

  -- Shorthand for single-variable type substitutions
  _[/_] : ∀ {ν η} → Type (suc ν) η → Type ν η → Type ν η
  a [/ b ] = a / sub b

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
open EffectsEffectsSubst public using ()
  renaming (_/_ to _/ef_; weaken to ef-weaken; _[/_] to _[/ef_])
open ContextTypeSubst public using ()
  renaming (_/_ to _ctx/tp_; weaken to ctx-tp-weaken)
open ContextEffectSubst public using ()
  renaming (_/_ to _ctx/ef_; weaken to ctx-ef-weaken)
