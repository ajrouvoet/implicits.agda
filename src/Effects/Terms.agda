module Effects.Terms where

open import Prelude

infixl 8 _∪_ _→[_]_ _·_ _[_]

data Effect (η : ℕ) : Set where

  evar : Fin η → Effect η

  IO : Effect η
  Reads : Effect η
  Writes : Effect η
  Throws : Effect η
  Pure : Effect η

  -- summing effects
  _∪_ : Effect η → Effect η → Effect η

  -- effect abstraction
  H : Effect (suc η) → Effect η

data Type (ν η : ℕ) : Set where

  void : Type ν η
  tvar : Fin ν → Type ν η
  _→[_]_ : Type ν η → Effect η → Type ν η → Type ν η

  -- type abstraction
  ∀'   : Type (suc ν) η → Type ν η

data Term (ν η n : ℕ) : Set where

  -- some primitives that perform effectful computations
  print : Term ν η n -- io
  throw : Term ν η n -- exception
  write : Term ν η n -- write heap
  read  : Term ν η n -- read heap

  -- variables
  var : Fin n → Term ν η n

  -- term abstraction & application
  λ'  : Type ν η → Term ν η (suc n) → Term ν η n
  _·_ : Term ν η n → Term ν η n → Term ν η n

  -- type abstraction & application
  Λ    : Term (suc ν) η n → Term ν η n
  _[_] : Term ν η n → Type ν η → Term ν η n

  -- effect abstraction & applixation
  H   : Term ν (suc η) n → Term ν η n
  _!_ : Term ν η n → Effect η → Term ν η n

Ctx : ℕ → ℕ → ℕ → Set
Ctx ν η n = Vec (Type ν η) n
  
