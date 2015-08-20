module Implicits.Oliveira.Types (TC : Set) where

open import Prelude hiding (lift; id)
open import Data.Fin.Substitution
open import Data.Nat.Properties as NatProps
open import Data.Star using (Star; ε; _◅_)
open import Extensions.Nat
import Data.Vec
  
infixr 10 _→'_
infixr 10 _⇒_
 
mutual
  data SimpleType (ν : ℕ) : Set where
    tc   : TC → SimpleType ν
    tvar : (n : Fin ν) → SimpleType ν
    _→'_ : Type ν → Type ν → SimpleType ν

  data Type (ν : ℕ) : Set where
    simpl : SimpleType ν → Type ν
    _⇒_  : Type ν → Type ν → Type ν
    ∀'   : Type (suc ν) → Type ν

is-∀' : ∀ {ν} → Type ν → Set
is-∀' (simpl x) = ⊥
is-∀' (_ ⇒ _) = ⊥
is-∀' (∀' x) = ⊤

fvars : ∀ {ν} → Type ν → List (Fin ν)
fvars (simpl (tc x)) = List.[]
fvars (simpl (tvar n)) = n List.∷ List.[]
fvars (simpl (x →' y)) = fvars x List.++ fvars y
fvars (a ⇒ b) = fvars a List.++ fvars b
fvars (∀' a) = List.gfilter (λ{ (Fin.zero) → nothing; (suc n) → just n}) (fvars a)

module Functions where

  -- proposition that states that the given polytype
  -- is a (possibly polymorphic) function
  data IsFunction {ν : ℕ} : Type ν → Set where
    lambda : (a b : Type ν) → IsFunction (simpl $ a →' b)
    ∀'-lambda : ∀ {f} → IsFunction f → IsFunction (∀' f)

  -- decision procedure for IsFunction
  is-function : ∀ {ν} → (a : Type ν) → Dec (IsFunction a)
  is-function (simpl (tc _)) = no (λ ())
  is-function (simpl (tvar n)) = no (λ ())
  is-function (simpl (a →' b)) = yes (lambda a b)
  is-function (x ⇒ x₁) = no (λ ())
  is-function (∀' a) with is-function a
  is-function (∀' a) | yes a-is-f = yes $ ∀'-lambda a-is-f
  is-function (∀' a) | no a-not-f = no (λ{ (∀'-lambda a-is-f) → a-not-f a-is-f })

  domain : ∀ {ν} {f : Type ν} → IsFunction f → Type ν
  domain (lambda a b) = a
  domain (∀'-lambda f) = ∀' (domain f)

  codomain : ∀ {ν} {f : Type ν} → IsFunction f → Type ν
  codomain (lambda a b) = b
  codomain (∀'-lambda f) = ∀' (codomain f)

module Rules where

  -- proposition that states that the given polytype
  -- is a (possibly polymorphic) rule type
  data IsRule {ν : ℕ} : Type ν → Set where
    rule : (a b : Type ν) → IsRule (a ⇒ b)
    ∀'-rule : ∀ {f} → IsRule f → IsRule (∀' f)

  -- decision procedure for IsRule
  is-rule : ∀ {ν} → (a : Type ν) → Dec (IsRule a)
  is-rule (simpl (tc _)) = no (λ ())
  is-rule (simpl (tvar n)) = no (λ ())
  is-rule (simpl (a →' b)) = no (λ ())
  is-rule (a ⇒ b)  = yes (rule a b)
  is-rule (∀' a) with is-rule a
  is-rule (∀' a) | yes a-is-f = yes $ ∀'-rule a-is-f
  is-rule (∀' a) | no a-not-f = no (λ{ (∀'-rule a-is-f) → a-not-f a-is-f })

  domain : ∀ {ν} {f : Type ν} → IsRule f → Type ν
  domain (rule a b) = a
  domain (∀'-rule f) = ∀' (domain f)

  codomain : ∀ {ν} {f : Type ν} → IsRule f → Type ν
  codomain (rule a b) = b
  codomain (∀'-rule f) = ∀' (codomain f)

  to-function : ∀ {ν} {f : Type ν} → IsRule f → Type ν
  to-function (rule a b) = simpl (a →' b)
  to-function (∀'-rule f) = ∀' (to-function f)
