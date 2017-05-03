module LF.Eval where

open import LF.Syntax
open import LF.Welltyped

-- term reductions
data _≻_ {n} : (t t' : Term n) → Set where
  -- reflexivity
  refl : ∀ {x} → x ≻ x

  -- beta reduction
  β : ∀ {A x x' b b'} → x ≻ x' → b ≻ b' → ((ƛ A x) · b) ≻ (x' / (sub b'))

  -- closure
  abs : ∀ {A e e'} → e ≻ e' → (ƛ A e) ≻ (ƛ A e')
  _·_ : ∀ {e e' t t'} → e ≻ e' → t ≻ t' → (t · e) ≻ (t' · e')

open import Data.Star
open import Data.Sum
open import Data.Product

-- reflexive-transitive closure of _≻_
_≻⋆_ : ∀ {n} (t t' : Term n) → Set
t ≻⋆ t' = Star _≻_ t t'

-- term equality in terms of reductions
_≡tm_ : ∀ {n} → (a b : Term n) → Set
a ≡tm b = a ≻⋆ b ⊎ b ≻⋆ a

-- Church-Rosser
-- diamond : ∀ {n} {u u' u'' : Term n} → u ≻ u' → u ≻ u'' → ∃ λ v → (u' ≻ v × u'' ≻ v)
-- church-rosser : ∀ {n} {u u' u'' : Term n} → u ≻⋆ u' → u ≻⋆ u'' → ∃ λ v → (u' ≻⋆ v × u'' ≻⋆ v)
