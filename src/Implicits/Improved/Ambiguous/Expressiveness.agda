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

module IdDerives where
  open import Implicits.Improved.Ambiguous.Resolution TC _tc≟_
  -- proof that polymorphic id derives every type
  -- this corresponds to the non-terminating expression:
  --   x : ∀ {a : Set} → a
  --   x = x
  --
  -- together with ⊇-oliveira-ambiguous, this shows that the coinductive ambiguous rules
  -- are more expressive then the inductive ambiguous rules.
  -- We could easily prove it for simple types, because the empty implicit context
  -- can only build rule types in the inductive case.

  tid : ∀ {n} → Type n
  tid = (∀' (simpl (tvar zero) ⇒ simpl (tvar zero)))

  [tid]⊢a : ∀ {ν} {a : Type ν} → (tid List.∷ List.[]) ⊢ᵣ a
  [tid]⊢a {a = a} = r-iapp (♯ (r-tapp a (♯ (r-ivar (here refl))))) (♯ [tid]⊢a)

  -- we can even derive it from an empty context, because we can derive identity from nothing:
  []⊢tid : ∀ {ν} → List.[] ⊢ᵣ tid {ν}
  []⊢tid = r-tabs (♯ (r-iabs (♯ (r-ivar (here refl)))))

  []⊢a : ∀ {ν} {a : Type ν} → List.[] ⊢ᵣ a
  []⊢a {a} = r-iapp (♯ r-iabs (♯ [tid]⊢a)) (♯ []⊢tid)
