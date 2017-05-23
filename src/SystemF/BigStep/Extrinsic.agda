module SystemF.BigStep.Extrinsic where

open import Prelude hiding (⊥; id)
open import Function as Fun using ()
open import Data.List hiding ([_]; monad)
open import Data.List.Properties as ListProp using ()
open import Data.Fin.Substitution
open import Extensions.List

open import SystemF.BigStep.Types

-- erased System F syntax
infix 100 _[_]
data Term : Set where
  unit : Term
  ƛ : Term → Term
  Λ : Term → Term
  _·_ : Term → Term → Term
  _[-] : Term → Term
  var : ℕ → Term

Ctx : ℕ → Set
Ctx n = List (Type n)

infixl 30 _ctx/_
_ctx/_ : ∀ {n m} → Ctx n → Sub Type n m → Ctx m
Γ ctx/ ρ = map (flip _/_ ρ) Γ

-- weakening followed by sub disappears on contexts
ctx/-wk-sub≡id : ∀ {n} (Γ : Ctx n) a → (Γ ctx/ wk) ctx/ (sub a) ≡ Γ
ctx/-wk-sub≡id Γ a = begin
  _ ≡⟨ sym (ListProp.map-compose Γ) ⟩
  map (λ x → x / wk / (sub a)) Γ ≡⟨ ListProp.map-cong Lemmas.wk-sub-vanishes Γ ⟩
  map Fun.id Γ ≡⟨ ListProp.map-id Γ ⟩
  _ ∎

-- weakening commutes with other substitutions on contexts
ctx/-wk-comm : ∀ {n m} (Γ : Ctx n) (ρ : Sub Type n m) → (Γ ctx/ ρ) ctx/ wk ≡ Γ ctx/ wk ctx/ (ρ ↑)
ctx/-wk-comm Γ ρ = begin
  _ ≡⟨ sym $ ListProp.map-compose Γ ⟩
  map (λ x → x / ρ / wk) Γ ≡⟨ ListProp.map-cong Lemmas.wk-commutes Γ ⟩
  map (λ x → x / wk / ρ ↑) Γ ≡⟨ ListProp.map-compose Γ ⟩
  _ ∎

data _⊢_∶_ {n}(Γ : Ctx n) : Term → Type n → Set where

  unit : -------------------
         Γ ⊢ unit ∶ Unit

  ƛ : ∀ {b t} a →
      (a ∷ Γ) ⊢ t ∶ b →
      -------------------
      Γ ⊢ ƛ t ∶ (a ⇒ b)

  var : ∀ {a i} →
      Γ [ i ]= a →
      -------------
      Γ ⊢ var i ∶ a

  _·_ : ∀ {f e a b} →
      Γ ⊢ f ∶ (a ⇒ b) →
      Γ ⊢ e ∶ a →
      ---------------
      Γ ⊢ f · e ∶ b

  Λ : ∀ {a t} →
      (Γ ctx/ wk) ⊢ t ∶ a →
      ---------------------
      Γ ⊢ Λ t ∶ ∀' a

  _[_] : ∀ {f a} →
      Γ ⊢ f ∶ (∀' a) →
      (b : Type n) →
      ---------------------------
      Γ ⊢ f [-] ∶ (a / (sub b))

_wt/_ : ∀ {n m}{Γ : Ctx n}{t a} → Γ ⊢ t ∶ a → (ρ : Sub Type n m) → (Γ ctx/ ρ) ⊢ t ∶ (a / ρ)
unit wt/ ρ = unit
ƛ a t wt/ ρ = ƛ (a / ρ) (t wt/ ρ)
var x wt/ ρ = var ([]=-map x)
(f · e) wt/ ρ = (f wt/ ρ) · (e wt/ ρ)
Λ t wt/ ρ = Λ (subst (λ Γ → Γ ⊢ _ ∶ _) (sym $ ctx/-wk-comm _ ρ) (t wt/ (ρ ↑)))
(_[_] {a = a} t b) wt/ ρ =
  subst (λ a → _ ⊢ _ ∶ a) (sym $ Lemmas.sub-commutes a) ((t wt/ ρ) [ (b / ρ) ])

-- environments
mutual
  Env : Set
  Env = List Val

  data Val : Set where
    unit : Val
    clos : Env → (t : Term) → Val
    tclos : Env → (t : Term) → Val

open import Relation.Binary.List.Pointwise hiding (refl)
mutual
  _⊢_ : ∀ {n} → Ctx n → Env → Set
  Γ ⊢ E = Rel (λ{ a v → ⊢̬ v ∶ a}) Γ E

  data ⊢̬_∶_ {n} : Val → Type n → Set where

    unit : -------------------
          ⊢̬ unit ∶ Unit

    clos : ∀ {b t}{Γ : Ctx n}{E a} →
            (a ∷ Γ) ⊢ t ∶ b →
            Γ ⊢ E →
            -------------------
            ⊢̬ clos E t ∶ (a ⇒ b)

    tclos : ∀ {a t}{Γ : Ctx n}{E} →
            (Γ ctx/ wk) ⊢ t ∶ a →
            Γ ⊢ E →
            ---------------------
            ⊢̬ tclos E t ∶ ∀' a

module StepIndexed where

  -- semantics in double-layered maybe monad;
  -- distinguishing semantic errors from timeouts

  open import Level as Lev using ()
  open import Data.Maybe
  open import Category.Monad
  open RawMonad (monad {f = Lev.zero})

  -- quadratic return through the layered monad
  pattern just² x = just (just x)

  -- substitution free semantics for SystemF
  _⊢_⇓_ : ∀ (μ : Env) → Term → ℕ → Maybe (Maybe Val)
  μ ⊢ x ⇓ zero = nothing
  μ ⊢ unit ⇓ (suc n) = just² unit
  μ ⊢ ƛ t ⇓ (suc n) = just² (clos μ t)
  μ ⊢ Λ t ⇓ (suc n) = just² (tclos μ t )
  μ ⊢ f · e ⇓ (suc n) with (μ ⊢ f ⇓ n) | μ ⊢ e ⇓ n
  -- timeout
  ... | nothing | _ = nothing
  ... | _ | nothing = nothing
  -- success
  ... | just² (clos μ' t) | just² v = (v ∷ μ') ⊢ t ⇓ n
  -- semantic errors & semantic error propagation
  ... | _ | _ = just nothing
  μ ⊢ t [-] ⇓ (suc n) with (μ ⊢ t ⇓ n)
  -- timeout
  ... | nothing = nothing
  -- success
  ... | just² (tclos μ' t') = μ' ⊢ t' ⇓ n
  -- semantic error (propagation)
  ... | _ = just nothing
  μ ⊢ var x ⇓ (suc n) = just (maybe-lookup x μ)

  -- extrinsic safety
  _⊢_⇓_ok : ∀ {n}{Γ : Ctx n}{μ : Env}{t a} →
            Γ ⊢ μ → Γ ⊢ t ∶ a → ∀ n → All (Any (λ v → ⊢̬ v ∶ a)) (μ ⊢ t ⇓ n)

  μ ⊢ x ⇓ zero ok = nothing

  μ ⊢ unit ⇓ suc n ok = just² unit

  μ ⊢ ƛ a x ⇓ suc n ok = just² (clos x μ)

  μ ⊢ Λ x ⇓ suc n ok = just² (tclos x μ)

  _⊢_⇓_ok {μ = E} μ (_·_ {f = f}{e = e} wtf wte) (suc n) with
    E ⊢ f ⇓ n | E ⊢ e ⇓ n | μ ⊢ wtf ⇓ n ok | μ ⊢ wte ⇓ n ok
  -- timeout
  ... | nothing | _ | _ | _ = nothing
  ... | just _ | nothing | _ | _ = nothing

  -- success
  ... | just² (clos μ' t) | just² v | just² (clos wtt wtμ') | just² px = (px ∷ wtμ') ⊢ wtt ⇓ n ok

  -- semantic error propagation
  ... | just nothing | _ | (just ()) | _
  ... | _ | just nothing | _ | (just ())

  -- semantic errors
  ... | just² (tclos _ _) | _ | just² () | _
  ... | just² unit | _ | just² () | _

  _⊢_⇓_ok {μ = E} μ (_[_] {f = f} wtf b) (suc n) with E ⊢ f ⇓ n | μ ⊢ wtf ⇓ n ok
  -- timeout
  ... | nothing | _ = nothing
  -- semantic errors
  ... | just nothing | (just ())
  ... | just² unit | just² ()
  ... | just² (clos x t) | just² ()
  -- success
  ... | just² (tclos μ' t) | just² (tclos tok μ'ok) =
    μ'ok ⊢ subst (λ Γ → Γ ⊢ _ ∶ _) (ctx/-wk-sub≡id _ b) (tok wt/ (sub b)) ⇓ n ok

  μ ⊢ var x ⇓ suc n ok with pointwise-maybe-lookup μ x
  μ ⊢ var x ⇓ suc n ok | _ , is-just , p rewrite is-just = just² p

module DelayMonad where

  open import Coinduction
  open import Category.Monad.Partiality
  open import Data.Maybe

  module _ where
    open Workaround

    _⊢lookup_ : Env → ℕ → Maybe Val
    [] ⊢lookup n = nothing
    (x ∷ μ) ⊢lookup zero = just x
    (x ∷ μ) ⊢lookup suc n = μ ⊢lookup n

    ret : ∀ {a} {A : Set a} → A → (Maybe A) ⊥P
    ret x = now (just x)

    -- substitution free semantics for SystemF
    _⊢_⇓P : ∀ (μ : Env) → Term → (Maybe Val) ⊥P
    μ ⊢ unit ⇓P = ret unit
    μ ⊢ ƛ t ⇓P = ret (clos μ t)
    μ ⊢ Λ t ⇓P = ret (tclos μ t )
    μ ⊢ f · e ⇓P = μ ⊢ f ⇓P >>= λ{
        (just (clos μ' t)) → μ ⊢ e ⇓P >>= (λ{
          (just v) → later (♯ ((v ∷ μ') ⊢ t ⇓P))
          ; nothing → now nothing
        }) ;
        _ → now nothing
      }
    μ ⊢ t [-] ⇓P = μ ⊢ t ⇓P >>= λ{
        (just (tclos μ' t')) →  later (♯ (μ' ⊢ t' ⇓P)) ;
        _ → now nothing
      }
    μ ⊢ var x ⇓P = now (μ ⊢lookup x)

    _⊢_⇓ : ∀ (μ : Env) → Term → (Maybe Val) ⊥
    μ ⊢ t ⇓ = ⟦ μ ⊢ t ⇓P ⟧P

{-}
  open import Category.Monad.Partiality.All
  open Alternative

  {-}
  module Compositional where
    private
      module Eq = Equality (_≡_)

    open import Level as Level
    open import Category.Monad
    open Eq hiding (_⇓)
    open RawMonad (monad {f = Level.zero})

    _·⇓_ : ∀ (f e : Val ⊥) → Val ⊥
    f ·⇓ e = f >>= λ{ (clos x t) → {!!} ; _ → now error }

    ·-comp : ∀ {μ f e} → (μ ⊢ f · e ⇓) ≅ ((μ ⊢ f ⇓) ·⇓ (μ ⊢ e ⇓))
    ·-comp = {!!}
  -}

  module Safety where

    _⊢_⇓okP : ∀ {n}{Γ : Ctx n}{μ : Env}{t a} → Γ ⊢ μ → Γ ⊢ t ∶ a → AllP (λ v → ⊢̬ v ∶ a) (μ ⊢ t ⇓)
    μ ⊢ unit ⇓okP = now unit
    μ ⊢ ƛ a t₁ ⇓okP = now (clos t₁ μ)
    μ ⊢ var x ⇓okP = now {!!}
    μ ⊢ f · e ⇓okP = {!μ ⊢ f ⇓okP!}
    μ ⊢ Λ t₁ ⇓okP = {!!}
    μ ⊢ t [ b ] ⇓okP = {!!}
-}
