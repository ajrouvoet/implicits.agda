module FSub.Intrinsic.Declarative.Syntax where

-- Welltyped syntax for Kernel F<: (Chap. 26/28 of TAPL)
-- We're using an declarative definition of subtyping.

open import Prelude
open import Data.Vec hiding (_>>=_; [_])
open import Extensions.Vec

open import FSub.Types
open import FSub.Types.Subtyping
open Declarative public

-- intrinsically typed syntax for FSub with explicit syntax for subsumption
data Term {n}(N : νCtx n)(Γ : Ctx n) : Type n → Set where
  unit : Term N Γ Unit
  ƛ    : ∀ {b} (a : Type n) → Term N (Γ +tm a) b → Term N Γ (a ⇒ b)
  Λ    : ∀ {a} u → Term (N +ν u) (Γ +ty) a → Term N Γ (∀≤ u a)
  _·_  : ∀ {a b} → Term N Γ (a ⇒ b) → Term N Γ a → Term N Γ b
  _[_] : ∀ {u a b} → Term N Γ (∀≤ u a) → N ⊢ b <: u → Term N Γ (a / sub b)
  var  : ∀ {a} → Var Γ a → Term N Γ a
  subm : ∀ {l u} → Term N Γ l → N ⊢ l <: u → Term N Γ u
