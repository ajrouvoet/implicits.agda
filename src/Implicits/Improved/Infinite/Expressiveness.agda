open import Prelude

module Implicits.Improved.Infinite.Expressiveness (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Coinduction
open import Data.Fin.Substitution
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.Deterministic.Resolution TC _tc≟_ as D
open import Implicits.Improved.Infinite.Resolution TC _tc≟_ as I 

module OliveiraDeterministic⊆Infinite where

  p : ∀ {ν n} {a : Type ν} {K : Ktx ν n} → K D.⊢ᵣ a → (proj₂ K) I.⊢ᵣ a
  p (r-simp x r↓a) = r-simp (proj₁ $ FirstLemmas.first⟶∈ x) (lem r↓a)
    where
        lem : ∀ {ν n} {K : Ktx ν n} {r a} → K D.⊢ r ↓ a → proj₂ K I.⊢ r ↓ a
        lem (i-simp a) = i-simp a
        lem (i-iabs x₁ x₂) = i-iabs (♯ (p x₁)) (lem x₂)
        lem (i-tabs b x₁) = i-tabs b (lem x₁)
  p (r-iabs ρ₁ x) = r-iabs (p x)
  p (r-tabs x) = r-tabs (p x)

  -- proof that polymorphic id derives every type
  -- this corresponds to the non-terminating expression:
  --   x : ∀ {a : Set} → a
  --   x = x

  tid : ∀ {n} → Type n
  tid = (∀' (simpl (tvar zero) ⇒ simpl (tvar zero)))

  tid↓a : ∀ {ν} {a : SimpleType ν} → (tid List.∷ List.[]) I.⊢ tid ↓ a
  tid↓a {a = a} = i-tabs (simpl a) (i-iabs (♯ (r-simp (here refl) tid↓a)) (i-simp a))

  [tid]⊢a : ∀ {ν} {a : Type ν} → (tid List.∷ List.[]) I.⊢ᵣ a
  [tid]⊢a {a = simpl x} = r-simp (here refl) tid↓a
  [tid]⊢a {a = a ⇒ b} = r-iabs (⊆-Δ⊢a [tid]⊢a sub)
    where
      sub : ∀ {a x} → a List.∈ (tid List.∷ List.[]) → a List.∈ (x List.∷ tid List.∷ List.[])
      sub (here px) = there (here px)
      sub (there ())
  [tid]⊢a {a = ∀' a} = r-tabs [tid]⊢a

  -- we can derive identity from nothing:
  []⊢tid : ∀ {ν} → List.[] I.⊢ᵣ tid {ν}
  []⊢tid = r-tabs (r-iabs (r-simp (here refl) (i-simp (tvar zero))))

  -- but interestingly, we CANNOT use this identity, and use it to derive everything else
  -- Because we can only derive (polymorphic) rule-types from an empty context.
  counter-example₁ : ¬ List.[] I.⊢ᵣ simpl (tvar {suc zero} zero)
  counter-example₁ (r-simp () _)
