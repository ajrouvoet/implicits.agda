open import Prelude hiding (subst)

module Implicits.Substitutions.MetaType where

open import Implicits.Syntax.Type
open import Implicits.Syntax.MetaType

open import Data.Fin.Substitution
open import Data.Star as Star hiding (map)
open import Data.Star.Properties
open import Data.Nat.Properties.Simple
open import Data.Vec hiding ([_])

module MetaTypeTypeSubst where

  MetaSub : (ℕ → ℕ → Set) → ℕ → ℕ → ℕ → Set
  MetaSub T m ν μ = Sub (T m) ν μ

  record MetaLift (T : ℕ → ℕ → Set) : Set where
    field
      simple : ∀ {m} → Simple (T m)
      lift : ∀ {m ν} → T m ν → MetaType m ν

  module MetaTypeApp {T} (l : MetaLift T) where
    open MetaLift l

    infixl 8 _/_

    mutual
      _s/_ : ∀ {m μ ν} → MetaSimpleType m ν → MetaSub T m ν μ → MetaType m μ
      tvar x s/ σ = lift (lookup x σ)
      mvar x s/ σ = simpl (mvar x)
      (a →' b) s/ σ = simpl ((a / σ) →' (b / σ))
      tc c s/ σ = simpl (tc c)

      _/_ : ∀ {m μ ν} → MetaType m ν → MetaSub T m ν μ → MetaType m μ
      simpl x / σ = (x s/ σ)
      (a ⇒ b) / σ = (a / σ) ⇒ (b / σ)
      (∀' a)   / σ = ∀' (a / σ ↑)
        where
          open Simple simple

    module _ {m : ℕ} where
      open Application (record { _/_ = _/_ {m = m} }) public using (_/✶_)
      open Simple (simple {m})

      →'-/✶-↑✶ : ∀ k {n n' a b} (ρs : Subs (T m) n n') →
              (simpl (a →' b)) /✶ ρs ↑✶ k ≡ simpl ((a /✶ ρs ↑✶ k) →' (b /✶ ρs ↑✶ k))
      →'-/✶-↑✶ k ε        = refl
      →'-/✶-↑✶ k (r ◅ ρs) = cong₂ _/_ (→'-/✶-↑✶ k ρs) refl

      ⇒-/✶-↑✶ : ∀ k {n n' a b} (ρs : Subs (T m) n n') →
              (a ⇒ b) /✶ ρs ↑✶ k ≡ (a /✶ ρs ↑✶ k) ⇒ (b /✶ ρs ↑✶ k)
      ⇒-/✶-↑✶ k ε        = refl
      ⇒-/✶-↑✶ k (r ◅ ρs) = cong₂ _/_ (⇒-/✶-↑✶ k ρs) refl

      tc-/✶-↑✶ : ∀ k {c n n'} (ρs : Subs (T m) n n') →
              (simpl (tc c)) /✶ ρs ↑✶ k ≡ simpl (tc c)
      tc-/✶-↑✶ k ε        = refl
      tc-/✶-↑✶ k (r ◅ ρs) = cong₂ _/_ (tc-/✶-↑✶ k ρs) refl 

      mvar-/✶-↑✶ : ∀ k {n n' c} (ρs : Subs (T m) n n') →
              (simpl (mvar c)) /✶ ρs ↑✶ k ≡ simpl (mvar c)
      mvar-/✶-↑✶ k ε        = refl
      mvar-/✶-↑✶ k (r ◅ ρs) = cong₂ _/_ (mvar-/✶-↑✶ k ρs) refl 

      ∀'-/✶-↑✶ : ∀ k {n n' a} (ρs : Subs (T m) n n') →
              (∀' a) /✶ ρs ↑✶ k ≡ ∀' (a /✶ ρs ↑✶ (suc k))
      ∀'-/✶-↑✶ k ε = refl
      ∀'-/✶-↑✶ k (x ◅ ρs) = cong₂ _/_ (∀'-/✶-↑✶ k ρs) refl

  Fin′ : ℕ → ℕ → Set
  Fin′ m ν = Fin ν

  module Lifted {m} {T} (lift : MetaLift T) where
    application : Application (MetaType m) (T m)
    application = record { _/_ = MetaTypeApp._/_ lift }

    open MetaLift lift public
    open Application application public
    open Simple (simple {m}) public

  varLift : MetaLift Fin′
  varLift = record {
      simple = record { var = Prelude.id ; weaken = suc }
      ; lift = (λ n → simpl (tvar n))
    }

  infixl 8 _/Var_

  _/Var_ : ∀ {m n k} → MetaType m n → Sub Fin n k → MetaType m k
  _/Var_ = MetaTypeApp._/_ varLift

  simple : ∀ {m} → Simple (MetaType m)
  simple = record { var = λ x → simpl (tvar x); weaken = λ x → x /Var VarSubst.wk }

  termLift : MetaLift MetaType
  termLift = record { simple = simple; lift = Prelude.id }

  private
    module ExpandSubst {n : ℕ} where
      app : Application (MetaType n) (MetaType n)
      app = record { _/_ = MetaTypeApp._/_ termLift }

      subst : Subst (MetaType n)
      subst = record
        { simple      = simple
        ; application = app
        }

      open Subst subst public

  open ExpandSubst public hiding (var; simple)

module MetaTypeMetaSubst where

  MetaSub : (ℕ → ℕ → Set) → ℕ → ℕ → ℕ → Set
  MetaSub T ν m m' = Sub (flip T ν) m m'

  record ExpandSimple (T : ℕ → ℕ → Set) : Set where
    field
      simple : ∀ {ν} → Simple (flip T ν)

    module _ {ν : ℕ} where
      open Simple (simple {ν}) public

  record ExpandApp (T : ℕ → ℕ → Set) : Set where
    field
      app : ∀ {ν} → Application (flip MetaType ν) (flip T ν)

    module _ {ν : ℕ} where
      open Application (app {ν}) public

  record MetaLift (T : ℕ → ℕ → Set) : Set where
    field
      exp-simple : ExpandSimple T
      lift : ∀ {m ν} → T m ν → MetaType m ν
      tpweaken : ∀ {m ν} → T m ν → T m (suc ν)

    open ExpandSimple exp-simple using (simple; _↑; weaken) renaming (var to evar)
    
    _↑tp : ∀ {m m' ν} → MetaSub T ν m m' → MetaSub T (suc ν) m m'
    _↑tp s = map tpweaken s

    field
      comm-weaken-tpweaken : ∀ {m ν} (a : T m ν) → weaken (tpweaken a) ≡ tpweaken (weaken a)
      tpweaken-var : ∀ {ν m} (n : Fin m) → (tpweaken {ν = ν} (evar n)) ≡ evar n

    _↑tp⋆_ : ∀ {m m' ν} → MetaSub T ν m m' → (k : ℕ) → MetaSub T (k + ν) m m'
    s ↑tp⋆ zero = s
    s ↑tp⋆ suc k = (s ↑tp⋆ k) ↑tp

  module MetaTypeApp {T} (l : MetaLift T) where
    open MetaLift l

    infixl 8 _/_

    mutual
      _s/_  : ∀ {m n ν} → MetaSimpleType m ν → MetaSub T ν m n → MetaType n ν
      tvar x s/ σ = simpl (tvar x)
      mvar x s/ σ = lift (lookup x σ)
      (a →' b) s/ σ = simpl ((a / σ) →' (b / σ))
      tc c s/ σ = simpl (tc c)

      _/_ : ∀ {m n ν} → MetaType m ν → MetaSub T ν m n → MetaType n ν
      simpl x / σ = (x s/ σ)
      (a ⇒ b) / σ = (a / σ) ⇒ (b / σ)
      (∀' a)   / σ = ∀' (a / σ ↑tp)

    open ExpandApp (record { app = record { _/_ = _/_ } }) hiding (_/_)
    open ExpandSimple exp-simple

  Fin′ : ℕ → ℕ → Set
  Fin′ m ν = Fin m

  module Lifted {T} (lift : MetaLift T) where
    open ExpandApp (record { app = record { _/_ = MetaTypeApp._/_ lift }}) public
    open MetaLift lift public
    open ExpandSimple exp-simple public

  module _ where
    private
      exp-simple : ExpandSimple Fin′
      exp-simple = record { simple = record { var = Prelude.id ; weaken = suc }}

    open ExpandSimple exp-simple

    varLift : MetaLift Fin′
    varLift = record {
        tpweaken = Prelude.id
        ; exp-simple = exp-simple
        ; lift = (λ n → simpl (mvar n))
        ; comm-weaken-tpweaken = λ s → refl
        ; tpweaken-var = λ n → refl }

  infixl 8 _/Var_

  _/Var_ : ∀ {m m' ν} → MetaType m ν → Sub Fin m m' → MetaType m' ν
  _/Var_ = MetaTypeApp._/_ varLift

  simple : ∀ {ν} → Simple (flip MetaType ν)
  simple = record { var = λ x → simpl (mvar x); weaken = λ x → x /Var VarSubst.wk }

  module _ where
    exp-simple : ExpandSimple MetaType
    exp-simple = record { simple = simple }

    open ExpandSimple exp-simple
    module MTTS = MetaTypeTypeSubst

    _↑⋆tp_ : ∀ {m m' ν} → MetaSub MetaType ν m m' → ∀ k → MetaSub MetaType (k + ν) m m'
    x ↑⋆tp zero = x
    x ↑⋆tp (suc k) = map MTTS.weaken (x ↑⋆tp k)

    _↑tp : ∀ {m m' ν} → MetaSub MetaType ν m m' → MetaSub MetaType (suc ν) m m'
    x ↑tp = x ↑⋆tp 1

    tp-weaken = MTTS.weaken

    comm-tp/var-/var : ∀ {ν ν' m m'} (a : MetaType m ν) {s : Sub Fin ν ν'} {s' : Sub Fin m m'} →
                       (a MTTS./Var s) /Var s' ≡ (a /Var s') MTTS./Var s
    comm-tp/var-/var (a ⇒ b) = cong₂ _⇒_ (comm-tp/var-/var a) (comm-tp/var-/var b)
    comm-tp/var-/var (∀' a) = cong ∀' (comm-tp/var-/var a)
    comm-tp/var-/var (simpl (tvar x)) = refl
    comm-tp/var-/var (simpl (mvar x)) = refl
    comm-tp/var-/var (simpl (a →' b)) = cong₂ (λ u v → simpl (u →' v)) (comm-tp/var-/var a)
                                          (comm-tp/var-/var b)
    comm-tp/var-/var (simpl (tc c)) = refl

    comm-weaken-tpweaken : ∀ {m ν} (a : MetaType m ν) → weaken (tp-weaken a) ≡ tp-weaken (weaken a)
    comm-weaken-tpweaken (a ⇒ b) = cong₂ _⇒_ (comm-weaken-tpweaken a) (comm-weaken-tpweaken b)
    comm-weaken-tpweaken (∀' a) = cong ∀' (comm-tp/var-/var a)
    comm-weaken-tpweaken (simpl (tvar x)) = refl
    comm-weaken-tpweaken (simpl (mvar x)) = refl
    comm-weaken-tpweaken (simpl (a →' b)) = cong₂ (λ u v → simpl (u →' v)) (comm-weaken-tpweaken a)
                                              (comm-weaken-tpweaken b)
    comm-weaken-tpweaken (simpl (tc c)) = refl

    open import Data.Vec.Properties

    termLift : MetaLift MetaType
    termLift = record {
        tpweaken = MetaTypeTypeSubst.weaken
        ; exp-simple = exp-simple
        ; lift = Prelude.id 
        ; comm-weaken-tpweaken = comm-weaken-tpweaken
        ; tpweaken-var = λ n → refl}

  private
    module ExpandSubst {n : ℕ} where
      app : Application (flip MetaType n) (flip MetaType n)
      app = record { _/_ = MetaTypeApp._/_ termLift }

      subst : Subst (flip MetaType n)
      subst = record
        { simple      = simple
        ; application = app
        }

      open Subst subst public

  open ExpandSubst public hiding (var; simple)

  open-meta-k : ∀ {m ν} k → (a : MetaType m (k + suc ν)) → MetaType (suc m) (k + ν)
  open-meta-k {m} {ν} k a = (weaken a) MetaTypeTypeSubst./ 
      (MetaTypeTypeSubst.sub (simpl (mvar zero)) MetaTypeTypeSubst.↑⋆ k)

  open-meta : ∀ {m ν} → (a : MetaType m (suc ν)) → MetaType (suc m) ν
  open-meta a = open-meta-k zero a

  _◁m₁ : ∀ {ν m} (r : MetaType m ν) → ℕ
  _◁m₁ (a ⇒ b) = b ◁m₁ 
  _◁m₁ (∀' r) = 1 + r ◁m₁ 
  _◁m₁ (simpl x) = zero

  -- heads of metatypes
  _◁m : ∀ {ν m} (r : MetaType m ν) → (MetaType ((r ◁m₁) + m) ν)
  (a ⇒ b) ◁m = b ◁m
  ∀' r ◁m = open-meta (r ◁m)
  simpl x ◁m = simpl x

  smeta-weaken : ∀ {m ν} → MetaSimpleType m ν → MetaSimpleType (suc m) ν
  smeta-weaken (tc x) = tc x
  smeta-weaken (tvar n) = tvar n
  smeta-weaken (mvar m) = mvar (suc m)
  smeta-weaken (a →' b) = weaken a →' weaken b
