open import Prelude

module Implicits.Improved.Finite.Expressiveness (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Coinduction
open import Data.Fin.Substitution
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.Deterministic.Resolution TC _tc≟_ as D
open import Implicits.Improved.Infinite.Resolution TC _tc≟_ as I 

{-
p : ∀ {ν n} {a : Type ν} {K : Ktx ν n} → K D.⊢ᵣ a → (proj₂ K) I.⊢ᵣ a
p (r-simp x r↓a) = r-simp (proj₁ $ FirstLemmas.first⟶∈ x) (lem r↓a)
  where
    lem : ∀ {ν n} {K : Ktx ν n} {r a} → K D.⊢ r ↓ a → (proj₂ K) I.⊢ r ↓ a
    lem (i-simp a) = i-simp a
    lem (i-iabs x₁ x₂) = i-iabs All.[] {!p x₁!} {!!}
    lem (i-tabs b x₁) = i-tabs b {!lem x₁!}
p (r-iabs ρ₁ x) = r-iabs (p x)
p (r-tabs x) = r-tabs (p x)
-}
