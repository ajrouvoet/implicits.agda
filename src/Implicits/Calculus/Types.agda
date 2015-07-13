module Implicits.Calculus.Types where

open import Prelude hiding (lift; id)
open import Data.Fin.Substitution
open import Data.Nat.Properties as NatProps
open import Data.Star using (Star; ε; _◅_)
open import Extensions.Nat
import Data.Vec
  
infixr 10 _→'_
infixr 10 _⇒_
data Type (ν : ℕ) : Set where
  tvar : (n : Fin ν) → Type ν
  _→'_ : Type ν → Type ν → Type ν
  _⇒_  : Type ν → Type ν → Type ν

data PolyType (ν : ℕ) : Set where
  mono : Type ν → PolyType ν
  ∀'   : PolyType (suc ν) → PolyType ν

is-∀' : ∀ {ν} → PolyType ν → Set
is-∀' (mono x) = ⊥
is-∀' (∀' x) = ⊤

is-mono : ∀ {ν} → PolyType ν → Set
is-mono (mono x) = ⊤
is-mono (∀' x) = ⊥

mono-totype : ∀ {ν} → (a : PolyType ν) → {ism : is-mono a} → Type ν
mono-totype (mono x) = x
mono-totype (∀' a) {ism = ()}

module Functions where

  -- proposition that states that the given polytype
  -- is a (possibly polymorphic) function
  data IsFunction {ν : ℕ} : PolyType ν → Set where
    lambda : (a b : Type ν) → IsFunction (mono $ a →' b)
    ∀'-lambda : ∀ {f} → IsFunction f → IsFunction (∀' f)

  -- decision procedure for IsFunction
  is-function : ∀ {ν} → (a : PolyType ν) → Dec (IsFunction a)
  is-function (mono (tvar n)) = no (λ ())
  is-function (mono (a →' b)) = yes (lambda a b)
  is-function (mono (x ⇒ x₁)) = no (λ ())
  is-function (∀' a) with is-function a
  is-function (∀' a) | yes a-is-f = yes $ ∀'-lambda a-is-f
  is-function (∀' a) | no a-not-f = no (λ{ (∀'-lambda a-is-f) → a-not-f a-is-f })

  domain : ∀ {ν} {f : PolyType ν} → IsFunction f → PolyType ν
  domain (lambda a b) = mono a
  domain (∀'-lambda f) = ∀' (domain f)

  codomain : ∀ {ν} {f : PolyType ν} → IsFunction f → PolyType ν
  codomain (lambda a b) = mono b
  codomain (∀'-lambda f) = ∀' (codomain f)

module Rules where

  -- proposition that states that the given polytype
  -- is a (possibly polymorphic) rule type
  data IsRule {ν : ℕ} : PolyType ν → Set where
    rule : (a b : Type ν) → IsRule (mono $ a ⇒ b)
    ∀'-rule : ∀ {f} → IsRule f → IsRule (∀' f)

  -- decision procedure for IsRule
  is-rule : ∀ {ν} → (a : PolyType ν) → Dec (IsRule a)
  is-rule (mono (tvar n)) = no (λ ())
  is-rule (mono (a →' b)) = no (λ ())
  is-rule (mono (a ⇒ b)) = yes (rule a b)
  is-rule (∀' a) with is-rule a
  is-rule (∀' a) | yes a-is-f = yes $ ∀'-rule a-is-f
  is-rule (∀' a) | no a-not-f = no (λ{ (∀'-rule a-is-f) → a-not-f a-is-f })

  domain : ∀ {ν} {f : PolyType ν} → IsRule f → PolyType ν
  domain (rule a b) = mono a
  domain (∀'-rule f) = ∀' (domain f)

  codomain : ∀ {ν} {f : PolyType ν} → IsRule f → PolyType ν
  codomain (rule a b) = mono b
  codomain (∀'-rule f) = ∀' (codomain f)

  to-function : ∀ {ν} {f : PolyType ν} → IsRule f → PolyType ν
  to-function (rule a b) = mono $ a →' b
  to-function (∀'-rule f) = ∀' (to-function f)
