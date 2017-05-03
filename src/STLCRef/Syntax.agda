module STLCRef.Syntax where

open import Prelude hiding (subst)
open import Data.Vec
open import Data.List
open import Function

data Type : Set where
  Unit : Type
  _⇒_  : (a b : Type) → Type
  Ref  : Type → Type

infixl 10 _·_
data Exp : (n : ℕ) → Set where
  unit : ∀ {n} → Exp n
  var  : ∀ {n} → Fin n → Exp n
  loc  : ∀ {n} → ℕ → Exp n
  ƛ    : ∀ {n} → Type → Exp (suc n) → Exp n
  _·_  : ∀ {n} → (f e : Exp n) → Exp n
  ref  : ∀ {n} → (e : Exp n) → Exp n
  !_   : ∀ {n} → (e : Exp n) → Exp n
  _≔_  : ∀ {n} → (x y : Exp n) → Exp n


data Val : ∀ {n} → Exp n → Set where
  unit : ∀ {n} → Val {n} unit
  ƛ    : ∀ {n} A → (e : Exp (suc n)) → Val (ƛ A e)
  loc  : ∀ {n} i → Val {n} (loc i)

Store : ℕ → Set
Store n = List (∃ λ (e : Exp n) → Val e)

open import Data.Fin.Substitution

module ExpApp {T} (l : Lift T Exp) where
  open Lift l

  _/_ : ∀ {n n'} → Exp n → Sub T n n' → Exp n'
  var x / s = lift $ lookup x s
  ƛ A t / s = ƛ A (t / (s ↑))
  (f · e) / s = (f / s) · (e / s)
  unit / s = unit
  loc x / s = loc x
  ref e / s = ref (e / s)
  (! e) / s = ! (e / s)
  (e ≔ e₁) / s = (e / s) ≔ (e₁ / s)

  open Application (record { _/_ = _/_ }) using (_/✶_)

tmSubst : TermSubst Exp
tmSubst = record { var = var; app = ExpApp._/_ }

open TermSubst tmSubst hiding (var) public
