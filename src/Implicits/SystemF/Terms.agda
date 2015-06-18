module Implicits.SystemF.Terms where
  
open import Prelude
open import Implicits.SystemF.Types

infixl 9 _[_] _·_
data Term (ν n : ℕ) : Set where
  var  : (x : Fin n) → Term ν n
  Λ    : Term (suc ν) n → Term ν n
  λ'   : Type ν → Term ν (suc n) → Term ν n
  _[_] : Term ν n → Type ν → Term ν n
  _·_  : Term ν n → Term ν n → Term ν n
