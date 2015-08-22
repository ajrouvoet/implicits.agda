open import Prelude hiding (lift; Fin′; subst)

module Implicits.Oliveira.Terms (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Data.Fin.Substitution
open import Implicits.Oliveira.Types TC _tc≟_

infixl 9 _[_] _·_
data Term (ν n : ℕ) : Set where
  var  : (x : Fin n) → Term ν n
  new  : TC → Term ν n
  Λ    : Term (suc ν) n → Term ν n
  λ'   : Type ν → Term ν (suc n) → Term ν n
  _[_] : Term ν n → Type ν → Term ν n
  _·_  : Term ν n → Term ν n → Term ν n

  -- rule abstraction and application
  ρ    : Type ν → Term ν (suc n) → Term ν n
  _⟨_⟩  : Term ν n → Term ν n → Term ν n
  ¿_   : Type ν → Term ν n

  -- ml-style bindings
  let'_in'_ : Term ν n → Term ν (suc n) → Term ν n
  implicit_in'_ : Term ν n → Term ν (suc n) → Term ν n

ClosedTerm : Set
ClosedTerm = Term 0 0
