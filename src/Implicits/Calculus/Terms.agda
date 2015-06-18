module Implicits.Calculus.Terms where
  
open import Prelude hiding (lift; Fin′; subst)
open import Data.Fin.Substitution
open import Implicits.Calculus.Types

infixl 9 _[_] _·_
data Term (ν n : ℕ) : Set where
  var  : (x : Fin n) → Term ν n
  Λ    : Term (suc ν) n → Term ν n
  λ'   : Type ν → Term ν (suc n) → Term ν n
  _[_] : Term ν n → Type ν → Term ν n
  _·_  : Term ν n → Term ν n → Term ν n
  
  -- rule abstraction and application
  ρ    : Type ν → Term ν (suc n) → Term ν n
  _⟨⟩  : Term ν n → Term ν n

  -- put value in implicit scope
  let'_in'_ : Term ν n → Term ν (suc n) → Term ν n
  implicit_in'_ : Term ν n → Term ν (suc n) → Term ν n

ClosedTerm : Set
ClosedTerm = Term 0 0
