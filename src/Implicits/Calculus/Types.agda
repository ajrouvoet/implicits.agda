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
