module Implicits.Oliveira.Substitutions (TC : Set) where

open import Prelude hiding (lift; Fin′; subst)
open import Implicits.Oliveira.Types TC 
open import Implicits.Oliveira.Terms TC 
open import Implicits.Oliveira.Contexts TC 
open import Data.Fin.Substitution
open import Data.Star hiding (map)

module TypeSubst where
  module TypeApp {T} (l : Lift T Type) where
    open Lift l hiding (var)

    infixl 8 _/_

    mutual 
      _/_ : ∀ {m n} → Type m → Sub T m n → Type n
      (simpl (tvar x)) / σ = lift (lookup x σ)
      (simpl (tc c)) / σ = simpl (tc c)
      (simpl (a →' b)) / σ = simpl ((a / σ) →' (b / σ))
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
  typeSubst = record { var = simpl ∘ tvar; app = TypeApp._/_ }


  open TermSubst typeSubst public hiding (var)

  infix 8 _[/_]

  -- Shorthand for single-variable type substitutions
  _[/_] : ∀ {n} → Type (suc n) → Type n → Type n
  a [/ b ] = a / sub b

  -- shorthand for type application
  infixl 8 _∙_
  _∙_ : ∀ {ν} → (a : Type ν) → {is∀ : is-∀' a} → Type ν → Type ν
  _∙_ (simpl (tvar n)) {is∀ = ()} _
  _∙_ (simpl (tc c)) b = simpl $ tc c
  _∙_ (simpl (_ →' _)) {is∀ = ()} _
  _∙_ (∀' x) b = x [/ b ]
  _∙_ (_ ⇒ _) {is∀ = ()} _

module TermTypeSubst where

  module TermTypeApp {T} (l : Lift T Type) where
    open Lift l hiding (var)
    open TypeSubst.TypeApp l renaming (_/_ to _/tp_)

    infixl 8 _/_

    -- Apply a type substitution to a term
    _/_ : ∀ {ν μ n} → Term ν n → Sub T ν μ → Term μ n
    new c      / σ = new c
    var x      / σ = var x
    Λ t        / σ = Λ (t / σ ↑)
    λ' a t     / σ = λ' (a /tp σ) (t / σ)
    t [ a ]    / σ = (t / σ) [ a /tp σ ]
    s · t      / σ = (s / σ) · (t / σ)
    ρ a t      / σ = ρ (a /tp σ) (t / σ)
    r ⟨ a ⟩     / σ = (r / σ) ⟨ a / σ ⟩
    ¿ a        / σ = ¿ (a /tp σ)
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
    new c      / σ = new c
    var x      / σ = lift $ lookup x σ
    Λ t        / σ = Λ (t / σ ↑tp)
    λ' a t     / σ = λ' a (t / σ ↑tm)
    t [ a ]    / σ = (t / σ) [ a ]
    s · t      / σ = (s / σ) · (t / σ)
    ρ a t      / σ = ρ a (t / σ ↑tm)
    r ⟨ t ⟩     / σ = (r / σ) ⟨ t / σ ⟩
    ¿ a        / σ = ¿ a
    implicit e in' e' / σ = implicit (e / σ) in' (e' / σ ↑tm)
    let' e in' e' / σ = let' (e / σ) in' (e' / σ ↑tm)

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

module KtxSubst where

  ktx-map : ∀ {ν μ n} → (Type ν → Type μ) →  Ktx ν n → Ktx μ n
  ktx-map f (Γ , Δ) = map f Γ , List.map f Δ

  _/_ : ∀ {ν μ n} → Ktx ν n → Sub Type ν μ → Ktx μ n
  K / σ = ktx-map (λ t → t TypeSubst./ σ) K

  _/Var_ : ∀ {ν m n} → Sub Fin n m → Ktx ν m → Ktx ν n
  σ /Var (Γ , Δ) = map (λ x → lookup x Γ) σ , Δ

  weaken : ∀ {ν n} → Ktx ν n → Ktx (suc ν) n
  weaken K = K / TypeSubst.wk

open TypeSubst public using (_∙_)
  renaming (_/_ to _tp/tp_; _[/_] to _tp[/tp_]; weaken to tp-weaken)
open TermTypeSubst public using ()
  renaming (_/_ to _tm/tp_; _[/_] to _tm[/tp_]; weaken to tm-weaken)
open TermTermSubst public using ()
  renaming (_/_ to _tm/tm_; _/Var_ to _tm/Var_; _[/_] to _tm[/tm_]; weaken to tmtm-weaken)
open KtxSubst public using (ktx-map)
  renaming (_/_ to _ktx/_; _/Var_ to _ktx/Var_; weaken to ktx-weaken)
