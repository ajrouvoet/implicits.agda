module Implicits.Syntactical.Terms where

open import Prelude hiding (lift; Fin′; subst)
open import Data.Fin.Substitution
open import Implicits.Syntactical.Types

infixl 9 _[_] _·_

mutual

  data Term (ν n : ℕ) : Set where
    var  : (x : Fin n) → Term ν n
    Λ    : Term (suc ν) n → Term ν n
    λ'   : Type ν → Term ν (suc n) → Term ν n
    _[_] : Term ν n → Type ν → Term ν n
    _·_  : Term ν n → Term ν n → Term ν n

    -- rule abstraction and application
    _⟨⟩  : Term ν n → Term ν n

    -- polymorphic let-binding
    let'_in'_ : Term ν n → Term ν (suc n) → Term ν n

    -- polymorphic implicit binding
    implicit_in'_ : ImplicitTerm ν n → Term ν (suc n) → Term ν n

  data ImplicitTerm (ν n : ℕ) : Set where
    val  : Term ν n → ImplicitTerm ν n
    rule : Term ν n → ImplicitTerm ν n

ClosedTerm : Set
ClosedTerm = Term 0 0
