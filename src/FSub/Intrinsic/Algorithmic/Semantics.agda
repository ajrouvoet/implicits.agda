module FSub.Intrinsic.Algorithmic.Semantics where

open import Prelude
open import FSub.Types
open import FSub.Intrinsic.Algorithmic.Syntax
open import Data.Product

Env : ∀ {n} → νCtx n → Ctx n → Set
data Val {n}(N : νCtx n) : Type n → Set where
  unit : Val {n} N Unit
  clos  : ∀ {a b Γ} → Env N Γ → Term N (Γ +tm a) b → Val N (a ⇒ b)
  tclos : ∀ {a Γ} u → Env N Γ → Term (N +ν u) (Γ +ty) a → Val N (∀≤ u a)

open import Data.List
open import Data.List.All as All hiding (map)

Env N Γ = All (λ u → ∃ λ l → Val N l × N ⊢ l <: u) Γ

module Canonical where

  ⇑×<:⇒ : ∀ {n N}{a b x xᵘ : Type n} → Val N x → N ⊢ x <: xᵘ → N ⊢ xᵘ ⇑ (a ⇒ b) →
          ∃₂ λ a' b' → x ≡ (a' ⇒ b')
  ⇑×<:⇒ () (ν-trans x p) ⇒-exp
  ⇑×<:⇒ () Bot<: ⇒-exp
  ⇑×<:⇒ v (a ⇒ b) ⇒-exp = _ , _ , refl
  ⇑×<:⇒ () ν-refl (ν _ _)
  ⇑×<:⇒ () (ν-trans _ _) (ν _ _)
  ⇑×<:⇒ () Bot<: (ν _ _)

open import Category.Monad.Partiality
open import Coinduction
open Workaround
open import Data.List.Any
open Membership-≡

module IgnoreSemantics where

-- Because we're doing an intrinsic version of algorithmic subtyping,
-- we have to weaken our preservation statement to some minimal value type.
-- Ultimately we're only interested at an erased version of the returned triple for the
-- runtime interpreter, which makes erasure very non-trivial.
_⊢_⇓P : ∀ {n N}{Γ : Ctx n}{a} → Env N Γ → Term N Γ a → (∃ λ l → Val N l × N ⊢ l <: a) ⊥P
E ⊢ unit ⇓P = now (, unit , <:-refl)
E ⊢ ƛ a t ⇓P = now (, clos E t , <:-refl)
E ⊢ Λ u t ⇓P = now (, tclos u E t , <:-refl)
E ⊢ _·[_,_]_ f a₁⇑⇒ a₃<:a₂ e ⇓P = (E ⊢ f ⇓P) >>=
  λ{ (s , v∈f , f<:a₁) → E ⊢ e ⇓P >>=
  λ{ (l , v∈l , l<:a₃) → later (♯ (eval v∈f f<:a₁ a₁⇑⇒ v∈l (<:-trans l<:a₃ a₃<:a₂))) }}
  where
    eval : ∀ {n x xᵘ y yᵘ b}{N : νCtx n} →
            Val N x → N ⊢ x <: xᵘ → N ⊢ xᵘ ⇑ (yᵘ ⇒ b) →
            Val N y → N ⊢ y <: yᵘ →
            (∃ λ l → Val N l × N ⊢ l <: b) ⊥P
    -- we have to prove a canonical value lemma to reveal the fact that
    -- the value can only be a closure
    eval () ν-refl (ν _ _)
    eval () (ν-trans _ _)
    eval () Bot<:
    eval (clos E' t) (a ⇒ b) ⇒-exp v∈y y-sub =
      -- now we have to use transitivity once to weaken the argument value
      -- enough such that it falls under the function domain bound
      ((, v∈y , <:-trans y-sub a) ∷ E') ⊢ t ⇓P >>= λ{
        -- ... and once to weaken the result value to make sure it falls under the
        -- range bound
        (l , v∈l , l<:b) → now (l , v∈l , <:-trans l<:b b)
      }
E ⊢ t [ p , q ] ⇓P = E ⊢ t ⇓P >>= (λ{ (l , v∈l , l<:a) → eval v∈l l<:a p q })
  where
    eval : ∀ {n}{N : νCtx n}{x xᵘ u a b} → Val N x → N ⊢ x <: xᵘ → N ⊢ xᵘ ⇑ (∀≤ u a) → N ⊢ b <: u →
            (∃ λ l → Val N l × N ⊢ l <: a / (sub b)) ⊥P
    eval unit () (ν _ _)
    eval (clos _ _) () (ν _ _)
    eval (tclos _ _ _) () (ν _ _)
    eval unit () ∀-exp _
    eval (clos _ _) () ∀-exp _
    eval (tclos u E t) (∀≤ p) ∀-exp z = {!!} -- TODO we need type in term substitution (under N)...
E ⊢ var x ⇓P = now (All.lookup E x)

module CoercionSemantics where
