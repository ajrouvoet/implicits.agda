module Implicits.SystemF.Types where

open import Prelude hiding (lift)
open import Data.Fin.Substitution
open import Extensions.Substitution
open import Data.Star using (Star; ε; _◅_)
  
infixl 10 _→'_
data Type (ν : ℕ) : Set where
  tvar : (n : Fin ν) → Type ν
  _→'_ : Type ν → Type ν → Type ν
  ∀'   : Type (suc ν) → Type ν
