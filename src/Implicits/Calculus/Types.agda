module Implicits.Calculus.Types where

open import Prelude hiding (lift; id)
open import Data.Fin.Substitution
open import Data.Nat.Properties as NatProps
open import Data.Star using (Star; ε; _◅_)
open import Extensions.Nat
import Data.Vec
  
data Type (ν : ℕ) : Set where
  tvar : (n : Fin ν) → Type ν
  _→'_ : Type ν → Type ν → Type ν
  _⇒_  : Type ν → Type ν → Type ν

data PolyType (ν : ℕ) : Set where
  mono : Type ν → PolyType ν
  ∀'   : PolyType (suc ν) → PolyType ν
