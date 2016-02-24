open import Prelude hiding (lift; Fin′; subst)

module Implicits.Syntax.Term where

open import Implicits.Syntax.Type

infixl 9 _[_] _·_
data Term (ν n : ℕ) : Set where
  var  : (x : Fin n) → Term ν n
  Λ    : Term (suc ν) n → Term ν n
  λ'   : Type ν → Term ν (suc n) → Term ν n
  _[_] : Term ν n → Type ν → Term ν n
  _·_  : Term ν n → Term ν n → Term ν n

  -- rule abstraction and application
  ρ    : Type ν → Term ν (suc n) → Term ν n
  _with'_ : Term ν n → Term ν n → Term ν n

  -- implicit rule application
  _⟨⟩  : Term ν n → Term ν n

ClosedTerm : Set
ClosedTerm = Term 0 0

-----------------------------------------------------------------------------
-- syntactic sugar

let'_∶_in'_ : ∀ {ν n} → Term ν n → Type ν → Term ν (suc n) → Term ν n
let' e₁ ∶ r in' e₂ = (λ' r e₂) · e₁

implicit_∶_in'_ : ∀ {ν n} → Term ν n → Type ν → Term ν (suc n) → Term ν n
implicit e₁ ∶ r in' e₂ = (ρ r e₂) with' e₁

¿_ : ∀ {ν n} → Type ν → Term ν n
¿ r = (ρ r (var zero)) ⟨⟩
