open import Prelude

module Implicits.Improved.Ambiguous.Expressiveness (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Coinduction
open import Data.Fin.Substitution
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_

module ⊇-oliveira-ambiguous where

  open import Implicits.Oliveira.Ambiguous.Resolution TC _tc≟_ as A
  open import Implicits.Improved.Ambiguous.Resolution TC _tc≟_ as I

  p : ∀ {ν n} {a : Type ν} {K : Ktx ν n} → K A.⊢ᵣ a → (proj₂ K) I.⊢ᵣ a
  p (r-tabs x) = r-tabs (♯ (p x))
  p (r-tapp a x) = r-tapp a (♯ (p x))
  p (r-ivar x) = r-ivar x
  p (r-iabs x) = r-iabs (♯ (p x))
  p (r-iapp x y) = r-iapp (♯ (p x)) (♯ p y)
