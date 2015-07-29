module Implicits.SystemF.Types (TC : Set) where

open import Prelude hiding (lift)
open import Data.Fin.Substitution
open import Extensions.Substitution
open import Data.Star using (Star; ε; _◅_)
  
infixl 10 _→'_
data Type (ν : ℕ) : Set where
  tc   : TC → Type ν
  tvar : (n : Fin ν) → Type ν
  _→'_ : Type ν → Type ν → Type ν
  ∀'   : Type (suc ν) → Type ν

module Functions where

  -- proposition that states that the given polytype
  -- is a (possibly polymorphic) function
  data IsFunction {ν : ℕ} : Type ν → Set where
    lambda : (a b : Type ν) → IsFunction (a →' b)
    ∀'-lambda : ∀ {f} → IsFunction f → IsFunction (∀' f)

  -- decision procedure for IsFunction
  is-function : ∀ {ν} → (a : Type ν) → Dec (IsFunction a)
  is-function (tc c) = no (λ ())
  is-function (tvar n) = no (λ ())
  is-function (a →' b) = yes (lambda a b)
  is-function (∀' a) with is-function a
  is-function (∀' a) | yes a-is-f = yes $ ∀'-lambda a-is-f
  is-function (∀' a) | no a-not-f = no (λ{ (∀'-lambda a-is-f) → a-not-f a-is-f })

  domain : ∀ {ν} {f : Type ν} → IsFunction f → Type ν
  domain (lambda a b) = a
  domain (∀'-lambda f) = ∀' (domain f)

  codomain : ∀ {ν} {f : Type ν} → IsFunction f → Type ν
  codomain (lambda a b) = b
  codomain (∀'-lambda f) = ∀' (codomain f)

open Functions public
