module Implicits.SystemF.Terms where
  
open import Prelude hiding (Fin′; subst) renaming (lift to finlift)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Implicits.SystemF.Types

infixl 9 _[_] _·_
data Term (ν n : ℕ) : Set where
  var  : (x : Fin n) → Term ν n
  Λ    : Term (suc ν) n → Term ν n
  λ'   : Type ν → Term ν (suc n) → Term ν n
  _[_] : Term ν n → Type ν → Term ν n
  _·_  : Term ν n → Term ν n → Term ν n

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


-- Lemmas about type substitutions in terms.
module TermTypeLemmas where
  open TermTypeSubst public

  private module T = TypeLemmas
  private module TS = TypeSubst
  private module V = VarLemmas

  /-↑⋆ :
    ∀ {T₁ T₂} {lift₁ : Lift T₁ Type} {lift₂ : Lift T₂ Type} →
    let open TS.Lifted lift₁ using () renaming (_↑⋆_ to _↑⋆₁_; _/_ to _/tp₁_)
        open   Lifted lift₁ using () renaming (_/_  to _/₁_)
        open TS.Lifted lift₂ using () renaming (_↑⋆_ to _↑⋆₂_; _/_ to _/tp₂_)
        open   Lifted lift₂ using () renaming (_/_  to _/₂_)
    in
    ∀ {n k} (ρ₁ : Sub T₁ n k) (ρ₂ : Sub T₂ n k) →
    (∀ i x → tvar x /tp₁ ρ₁ ↑⋆₁ i ≡ tvar x /tp₂ ρ₂ ↑⋆₂ i) →
     ∀ i {m} (t : Term (i N+ n) m)  → t /₁ ρ₁ ↑⋆₁ i ≡ t /₂ ρ₂ ↑⋆₂ i
  /-↑⋆ ρ₁ ρ₂ hyp i (var x)      = refl
  /-↑⋆ ρ₁ ρ₂ hyp i (Λ t)        = cong Λ      (/-↑⋆ ρ₁ ρ₂ hyp (1 N+ i) t)
  /-↑⋆ ρ₁ ρ₂ hyp i (λ' a t)     =
    cong₂ λ'     (T./-↑⋆ ρ₁ ρ₂ hyp i a)       (/-↑⋆ ρ₁ ρ₂ hyp i t)
  /-↑⋆ ρ₁ ρ₂ hyp i (t [ b ])    =
    cong₂ _[_]     (/-↑⋆ ρ₁ ρ₂ hyp i t)     (T./-↑⋆ ρ₁ ρ₂ hyp i b)
  /-↑⋆ ρ₁ ρ₂ hyp i (s · t)      =
    cong₂ _·_      (/-↑⋆ ρ₁ ρ₂ hyp i s)       (/-↑⋆ ρ₁ ρ₂ hyp i t)

  /-wk : ∀ {m n} (t : Term m n) → t / TypeSubst.wk ≡ weaken t
  /-wk t = /-↑⋆ TypeSubst.wk VarSubst.wk (λ k x → begin
    tvar x T./ T.wk T.↑⋆ k ≡⟨ T.var-/-wk-↑⋆ k x ⟩
    tvar (finlift k suc x) ≡⟨ cong tvar (sym (V.var-/-wk-↑⋆ k x)) ⟩
    tvar (lookup x (V.wk V.↑⋆ k)) ≡⟨ refl ⟩
    tvar x TS./Var V.wk V.↑⋆ k ∎) 0 t

module TermTermSubst where

  -- Substitutions of terms in terms
  TermSub : (ℕ → ℕ → Set) → ℕ → ℕ → ℕ → Set
  TermSub T ν m n = Sub (T ν) m n

  record TermLift (T : ℕ → ℕ → Set) : Set where
    infix 10 _↑tm _↑tp
    field
      lift : ∀ {ν n} → T ν n → Term ν n
      _↑tm : ∀ {ν m n} → TermSub T ν m n → TermSub T ν (suc m) (suc n)
      _↑tp : ∀ {ν m n} → TermSub T ν m n → TermSub T (suc ν) m n

  module TermTermApp {T} (l : TermLift T) where
    open TermLift l

    infixl 8 _/_

    -- Apply a term substitution to a term
    _/_ : ∀ {ν m n} → Term ν m → TermSub T ν m n → Term ν n
    var x      / σ = lift (lookup x σ)
    Λ t        / σ = Λ (t / (σ ↑tp))
    λ' a t     / σ = λ' a (t / σ ↑tm)
    t [ a ]    / σ = (t / σ) [ a ]
    s · t      / σ = (s / σ) · (t / σ)

  Fin′ : ℕ → ℕ → Set
  Fin′ _ m = Fin m

  varLift : TermLift Fin′
  varLift = record { lift = var; _↑tm = VarSubst._↑; _↑tp = id }

  infixl 8 _/Var_

  _/Var_ : ∀ {ν m n} → Term ν m → Sub Fin m n → Term ν n
  _/Var_ = TermTermApp._/_ varLift

  private
    module ExpandSimple {n : ℕ} where
      simple : Simple (Term n)
      simple = record { var = var; weaken = λ t → t /Var VarSubst.wk }

      open Simple simple public

  open ExpandSimple  using (_↑; simple)
  open TermTypeSubst using () renaming (weaken to weakenTp)

  termLift : TermLift Term
  termLift = record
    { lift = id; _↑tm = _↑ ; _↑tp = λ ρ → map weakenTp ρ }

  private
    module ExpandSubst {ν : ℕ} where
      app : Application (Term ν) (Term ν)
      app = record { _/_ = TermTermApp._/_ termLift {ν = ν} }

      subst : Subst (Term ν)
      subst = record
        { simple      = simple
        ; application = app
        }

      open Subst subst public

  open ExpandSubst public hiding (var; simple)

  infix 8 _[/_]

  -- Shorthand for single-variable term substitutions in terms
  _[/_] : ∀ {ν n} → Term ν (suc n) → Term ν n → Term ν n
  s [/ t ] = s / sub t

open TermTermSubst public using () renaming (_/_ to _tm/tm_; _[/_] to _tm[/tm_])
open TermTypeSubst public using () renaming (_/_ to _tm/tp_; _[/_] to _tm[/tp_]; weaken to tm-weaken)
