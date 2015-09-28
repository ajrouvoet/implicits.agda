open import Prelude hiding (lift; Fin′; subst; id)

module Implicits.Oliveira.Substitutions (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Types.Unification.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Data.Fin.Substitution
open import Data.Star as Star hiding (map)
open import Data.Star.Properties

module TypeSubst where
  module TypeApp {T} (l : Lift T Type) where
    open Lift l hiding (var)

    infixl 8 _/_

    mutual 
      _simple/_ : ∀ {m n} → SimpleType m → Sub T m n → Type n
      tc c simple/ σ = simpl (tc c)
      tvar x simple/ σ = lift (lookup x σ)
      (a →' b) simple/ σ = simpl ((a / σ) →' (b / σ))

      _/_ : ∀ {m n} → Type m → Sub T m n → Type n
      (simpl c) / σ = (c simple/ σ)
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
  typeSubst = record { var = (λ n → simpl (tvar n)); app = TypeApp._/_ }

  open TermSubst typeSubst public hiding (var)
  open TypeApp termLift public using (_simple/_)
  open TypeApp varLift public using () renaming (_simple/_ to _simple/Var_)

  infix 8 _[/_]

  -- Shorthand for single-variable type substitutions
  _[/_] : ∀ {n} → Type (suc n) → Type n → Type n
  a [/ b ] = a / sub b

  -- shorthand for type application
  infixl 8 _∙_
  _∙_ : ∀ {ν} → (a : Type ν) → {is∀ : is-∀' a} → Type ν → Type ν
  _∙_ (simpl (tvar n)) {is∀ = ()} _
  _∙_ (simpl (tc c)) b = simpl (tc c)
  _∙_ (simpl (_ →' _)) {is∀ = ()} _
  _∙_ (∀' x) b = x [/ b ]
  _∙_ (_ ⇒ _) {is∀ = ()} _

  stp-weaken : ∀ {ν} → SimpleType ν → SimpleType (suc ν)
  stp-weaken (tc x) = tc x
  stp-weaken (tvar n) = tvar (suc n)
  stp-weaken (a →' b) = weaken a →' weaken b

  private
    lem : ∀ y (x : Fin (suc y)) → ∃ λ a → y ≡ (toℕ x) N+ a
    lem zero zero = zero , refl
    lem zero (suc ())
    lem (suc x) zero = suc x , refl
    lem (suc x) (suc y) = , cong suc (proj₂ $ lem x y)

  embed : ∀ {ν} (α : Fin (suc ν)) → Sub Type (toℕ α) ν → Sub Type ν ν
  embed {ν} α s = Prelude.subst
    (λ u → Sub Type u ν)
    (sym eq)
    (s ++ (drop (toℕ α) (Prelude.subst (λ u → Vec (Type ν) u) eq (id {ν}))))
      where
          eq = proj₂ $ lem ν α

module KtxSubst where

  ktx-map : ∀ {ν μ n} → (Type ν → Type μ) →  Ktx ν n → Ktx μ n
  ktx-map f (Γ , Δ) = map f Γ , List.map f Δ

  _/_ : ∀ {ν μ n} → Ktx ν n → Sub Type ν μ → Ktx μ n
  K / σ = ktx-map (λ t → t TypeSubst./ σ) K

  _/Var_ : ∀ {ν m n} → Sub Fin n m → Ktx ν m → Ktx ν n
  σ /Var (Γ , Δ) = map (λ x → lookup x Γ) σ , Δ

  ictx-weaken : ∀ {ν} → ICtx ν → ICtx (suc ν)
  ictx-weaken Δ = List.map (flip TypeSubst._/_ TypeSubst.wk) Δ

  weaken : ∀ {ν n} → Ktx ν n → Ktx (suc ν) n
  weaken K = K / TypeSubst.wk

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
      _↑tp : ∀ {m m' ν} → MetaSub T ν m m' → MetaSub T (suc ν) m m'

    open ExpandSimple exp-simple using (simple; _↑)
    
    field
      comm-↑-↑tp : ∀ {ν n n'} (s : Sub (flip T ν) n n') → (s ↑) ↑tp ≡ (s ↑tp) ↑

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

  varLift : MetaLift Fin′
  varLift = record {
      _↑tp = Prelude.id
      ; exp-simple = record { simple = record { var = Prelude.id ; weaken = suc }}
      ; lift = (λ n → simpl (mvar n))
      ; comm-↑-↑tp = λ s → refl
    }

  infixl 8 _/Var_

  _/Var_ : ∀ {m m' ν} → MetaType m ν → Sub Fin m m' → MetaType m' ν
  _/Var_ = MetaTypeApp._/_ varLift

  simple : ∀ {ν} → Simple (flip MetaType ν)
  simple = record { var = λ x → simpl (mvar x); weaken = λ x → x /Var VarSubst.wk }

  module _ where
    exp-simple : ExpandSimple MetaType
    exp-simple = record { simple = simple }

    open ExpandSimple exp-simple

    _↑tp : ∀ {m m' ν} → MetaSub MetaType ν m m' → MetaSub MetaType (suc ν) m m'
    _↑tp = λ x → map MetaTypeTypeSubst.weaken x

    tp-weaken = MetaTypeTypeSubst.weaken

    comm-tp/var-/var : ∀ {ν ν' m m'} (a : MetaType m ν) {s : Sub Fin ν ν'} {s' : Sub Fin m m'} →
                       (a MetaTypeTypeSubst./Var s) /Var s' ≡ (a /Var s') MetaTypeTypeSubst./Var s
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
        _↑tp = _↑tp
        ; exp-simple = exp-simple
        ; lift = Prelude.id 
        ; comm-↑-↑tp = λ s → begin
          (s ↑) ↑tp
            ≡⟨ cong (λ u → simpl (mvar zero) ∷ u) (sym $ map-∘ tp-weaken weaken s) ⟩
          (simpl (mvar zero)) ∷ (map (tp-weaken ∘ weaken) s)
            ≡⟨ cong (λ u → simpl (mvar zero) ∷ u)
                 (sym $ map-cong comm-weaken-tpweaken s) ⟩
          (simpl (mvar zero)) ∷ (map (weaken ∘ tp-weaken) s)
            ≡⟨ cong (λ u → simpl (mvar zero) ∷ u) (map-∘ weaken tp-weaken s) ⟩
          s ↑tp ↑ ∎ }

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

  open-meta : ∀ {m ν} → (a : MetaType m (suc ν)) → MetaType (suc m) ν
  open-meta x = (weaken x) MetaTypeTypeSubst./ (MetaTypeTypeSubst.sub (simpl (mvar zero)))

  smeta-weaken : ∀ {m ν} → MetaSimpleType m ν → MetaSimpleType (suc m) ν
  smeta-weaken (tc x) = tc x
  smeta-weaken (tvar n) = tvar n
  smeta-weaken (mvar m) = mvar (suc m)
  smeta-weaken (a →' b) = weaken a →' weaken b

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
  varLift = record { lift = var; _↑tm = VarSubst._↑; _↑tp = Prelude.id }

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
    { lift = Prelude.id; _↑tm = _↑ ; _↑tp = λ ρ → map weakenTp ρ }

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

open TypeSubst public using (_∙_; stp-weaken)
  renaming (_simple/_ to _stp/tp_; _/_ to _tp/tp_; _[/_] to _tp[/tp_]; weaken to tp-weaken)
open TermTypeSubst public using ()
  renaming (_/_ to _tm/tp_; _[/_] to _tm[/tp_]; weaken to tm-weaken)
open TermTermSubst public using ()
  renaming (_/_ to _tm/tm_; _/Var_ to _tm/Var_; _[/_] to _tm[/tm_]; weaken to tmtm-weaken)
open KtxSubst public using (ktx-map; ictx-weaken)
  renaming (_/_ to _ktx/_; _/Var_ to _ktx/Var_; weaken to ktx-weaken)
