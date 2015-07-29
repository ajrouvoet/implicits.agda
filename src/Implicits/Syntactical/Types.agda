module Implicits.Syntactical.Types where

open import Prelude hiding (lift; id)
open import Data.Fin.Substitution
open import Data.Nat.Properties as NatProps
open import Data.Star using (Star; ε; _◅_)
open import Extensions.Nat
import Data.Vec

infixr 10 _→'_

data Type (ν : ℕ) : Set where
  tvar : (n : Fin ν) → Type ν
  _→'_ : Type ν → Type ν → Type ν
  ∀'   : Type (suc ν) → Type ν

is-∀' : ∀ {ν} → Type ν → Set
is-∀' (tvar x) = ⊥
is-∀' (_ →' _) = ⊥
is-∀' (∀' x) = ⊤

is-mono : ∀ {ν} → Type ν → Set
is-mono (tvar x) = ⊤
is-mono (_ →' _) = ⊤
is-mono (∀' x) = ⊥

module Functions where

  -- proposition that states that the given polytype
  -- is a (possibly polymorphic) function
  data IsFunction {ν : ℕ} : Type ν → Set where
    lambda : (a b : Type ν) → IsFunction (a →' b)
    ∀'-lambda : ∀ {f} → IsFunction f → IsFunction (∀' f)

  -- decision procedure for IsFunction
  is-function : ∀ {ν} → (a : Type ν) → Dec (IsFunction a)
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

data Implicit ν : Set where
  rule : ∀ {a : Type ν} → IsFunction a → Implicit ν
  val  : Type ν → Implicit ν

totype : ∀ {ν} → Implicit ν → Type ν
totype (rule {a} _) = a
totype (val x) = x
