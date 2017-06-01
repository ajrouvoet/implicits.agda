module SystemF.BigStep.Intrinsic where

open import Prelude hiding (⊥)

open import SystemF.BigStep.Types

open import Data.List hiding ([_])
open import Data.List.Any.Membership
open import Data.List.Any hiding (map)
open import Data.Fin.Substitution

-- intrinsically typed syntax for System F
infix 100 _[_]
data Term {n}(Γ : Ctx n) : Type n → Set where
  unit : Term Γ Unit
  ƛ : ∀ {b} (a : Type n) → Term (Γ +tm a) b → Term Γ (a ⇒ b)
  Λ : ∀ {a} → Term (Γ +ty) a → Term Γ (∀' a)
  _·_ : ∀ {a b} → Term Γ (a ⇒ b) → Term Γ a → Term Γ b
  _[_] : ∀ {a} → Term Γ (∀' a) → ∀ b → Term Γ (a / sub b)
  var : ∀ {a} → Var Γ a → Term Γ a

_tm/_ : ∀ {n m}{Γ : Ctx n}{a} → Term Γ a → (ρ : Sub Type n m) → Term (Γ ctx/ ρ) (a / ρ)
unit tm/ ρ = unit
ƛ a t tm/ ρ = ƛ (a / ρ) (t tm/ ρ)
Λ t tm/ ρ = Λ (subst (λ Γ → Term Γ _) (sym $ CtxLemmas.ctx/-wk-comm _ ρ) (t tm/ (ρ ↑)))
(f · e) tm/ ρ = (f tm/ ρ) · (e tm/ ρ)
(_[_] {a = a} t b) tm/ ρ =
  subst (λ a → Term _ a) (sym $ Lemmas.sub-commutes a) ((t tm/ ρ) [ b / ρ ])
var x tm/ ρ = var (Inverse.to map-∈↔ ⟨$⟩ (, (x , refl)))
  where
    open import Function.Equality
    open import Function.Inverse

module Semantics where

  Env : ∀ {n} → Ctx n → Set
  data Val {n} : Type n → Set where
    unit : Val {n} Unit
    clos  : ∀ {a b Γ} → Env Γ → Term (Γ +tm a) b → Val (a ⇒ b)
    tclos : ∀ {a Γ} → Env Γ → Term (Γ +ty) a → Val (∀' a)

  open import Data.List
  open import Data.List.All as All hiding (map)

  Env Γ = All Val Γ

  open import Category.Monad.Partiality
  open import Coinduction

  private
    open Workaround

    _⊢_⇓P : ∀ {n}{Γ : Ctx n}{a} → Env Γ → Term Γ a → (Val a) ⊥P
    C ⊢ unit ⇓P = now unit
    C ⊢ ƛ a t ⇓P = now (clos C t)
    C ⊢ Λ t ⇓P = now (tclos C t)
    C ⊢ f · e ⇓P =
      (C ⊢ f ⇓P) >>= λ{
        (clos C' fb) → (C ⊢ e ⇓P) >>= λ v → later (♯ ((v ∷ C') ⊢ fb ⇓P))
      }
    C ⊢ t [ ty ] ⇓P =
      (C ⊢ t ⇓P >>= λ{
        -- We have to substitute a type into the body here
        -- and proof that weakening + substitution disappears on the context.
        -- The context lemma is computationally irrelevant, but the
        -- type-in-term substitution is not as trivially irrelevant
        (tclos C' b) → later (♯ (
         (subst Env (sym $ CtxLemmas.ctx/-wk-sub≡id _ ty) C') ⊢ b tm/ sub ty ⇓P
        ))
      })
    C ⊢ var x ⇓P = now (lookup C x)

  -- definitional interpreter in the partiality monad
  _⊢_⇓ : ∀ {n}{Γ : Ctx n}{a} → Env Γ → Term Γ a → (Val a) ⊥
  C ⊢ t ⇓ = ⟦ C ⊢ t ⇓P ⟧P

module Example where

  open import Data.Fin renaming (zero to z; suc to s)
  open import Data.List hiding ([_])
  open import Data.List.Any
  open import Data.List.All
  open import Category.Monad.Partiality
  open Semantics

  id' : Term {0} [] (∀' (ν zero ⇒ ν zero))
  id' = Λ (ƛ (ν z) (var (here refl)))

  test = run ([] ⊢ ((id' [ Unit ]) · unit) ⇓) for 10 steps
