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
      -- DERP! We don't get our money's worth here at all!
      -- Even though we're writing an interpreter with an intrinsic preservation constraint
      -- we still have to "handle" semantic error cases to get case coverage;
      -- Update: since we had to weaken type-preservation to prove covariant function application,
      -- this becomes even more annoying! Not sure how this proof should proceed.
      eval : ∀ {n x xᵘ y yᵘ b}{N : νCtx n} →
             Val N x → N ⊢ x <: xᵘ → N ⊢ xᵘ ⇑ (yᵘ ⇒ b) →
             Val N y → N ⊢ y <: yᵘ →
             (∃ λ l → Val N l × N ⊢ l <: b) ⊥P
      eval v∈x x-sub ⇒-exp v∈y y-sub = {!!}
      eval v∈x x-sub (ν x₁ x-rev) v∈y y-sub = {!v∈x!}
      {-}
      eval (clos E' body) ⇒-exp sub v with narrow (here refl) sub body
      ... | a' , t∈a' , a'<:b = ((v ∷ E') ⊢ t∈a' ⇓P) >>= (
          λ{ (c , t∈c , c<:a') → now (c , t∈c , <:-trans c<:a' a'<:b )}
        )
      -}
  E ⊢ t [ p , q ] ⇓P = {!!}
  E ⊢ var x ⇓P = now (All.lookup E x)

module CoercionSemantics where
