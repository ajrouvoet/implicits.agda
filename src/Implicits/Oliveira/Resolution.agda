open import Prelude

module Implicits.Oliveira.Resolution
  (TC : Set)
  (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Data.Fin.Substitution
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Types.Unification TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.WellTyped TC _tc≟_
open import Extensions.ListFirst

module Lemmas where

  lem-A3 : ∀ {ν n} (K : Ktx ν n) {a r} → K ⟨ a ⟩= r → r List.∈ (proj₂ K)
  lem-A3 _ = proj₁ ∘ first⟶∈

  -- p'haps counterintuitively the following proposition is NOT a theorem:
  -- Δ⊢ᵣa⟶Δ≢Ø : ∀ {ν n} {K : Ktx ν n} {a} → K ⊢ᵣ a → ∃ λ b → b List.∈ (proj₂ K)
  -- since [] ⊢ᵣ Nat ⇒ Nat through the r-iabs rule, but also:
  -- [] ⊢ᵣ Nat ⇒ (Nat ⇒ Nat), etc; through recursion on r-iabs

open Lemmas

data _⊢_matches_ {ν} (ρs : List (Type ν)) : Type ν → SimpleType ν → Set where
  mtc-tabs : ∀ {r a} → List.map tp-weaken ρs ⊢ r matches (stp-weaken a) → ρs ⊢ ∀' r matches a
  mtc-iabs : ∀ {a b c} → (a List.∷ ρs) ⊢ b matches c → ρs ⊢ a ⇒ b matches c
  mtc-simp : ∀ {a b s} → (simpl a) tp/tp s ≡ simpl b → ρs ⊢ (simpl a) matches b

_⊢match1st_ : ∀ {ν n} (K : Ktx ν n) → (a : SimpleType ν) →
              Dec (∃ λ r → first r ∈ proj₂ K ⇔ (λ r' → List.[] ⊢ r' matches a))
(Γ , Δ) ⊢match1st a = find (λ r → List.[] ⊢ r matches a) (match List.[] a) Δ
  where
    match : ∀ {ν} → (ρs : List (Type ν)) → (a : SimpleType ν) → (r : Type ν) →
            Dec (ρs ⊢ r matches a)
    match ρs a (simpl x) with mgu (simpl x) (simpl a)
    match ρs a (simpl x) | yes (s , p) = yes (mtc-simp p)
    match ρs a (simpl x) | no ¬p = no (λ{ (mtc-simp x) → ¬p (, x) })
    match ρs a (b ⇒ c) with match (b List.∷ ρs) a c
    match ρs a (b ⇒ c) | yes p = yes $ mtc-iabs p
    match ρs a (b ⇒ c) | no ¬p = no (λ{ (mtc-iabs x) → ¬p x})
    match ρs a (∀' r) with match (List.map tp-weaken ρs) (stp-weaken a) r
    match ρs a (∀' r) | yes p = yes $ mtc-tabs p
    match ρs a (∀' r) | no ¬p = no (λ{ (mtc-tabs x) → ¬p x })

{-# NO_TERMINATION_CHECK #-}
_⊢alg_ : ∀ {ν n} (K : Ktx ν n) → (a : Type ν) → Dec (K ⊢ᵣ a)
K ⊢alg simpl x with K ⊢match1st x
K ⊢alg simpl x | yes (r , p) with K ⊢alg r
K ⊢alg simpl x | yes (r , p) | yes K⊢ᵣr = yes {!!} -- (r-simp p {!!})
K ⊢alg simpl x | yes (r , p) | no ¬K⊢ᵣr = {!!}
K ⊢alg simpl x | no ¬p = no {!!} -- (λ{ (r-simp fst r↓x) → ¬p (, fst) })
K ⊢alg (a ⇒ b) with (a ∷K K) ⊢alg b
K ⊢alg (a ⇒ b) | yes p = yes $ r-iabs a p
K ⊢alg (a ⇒ b) | no ¬p = no (λ{ (r-iabs .a x) → ¬p x })
K ⊢alg ∀' a with (ktx-weaken K) ⊢alg a
K ⊢alg ∀' a | yes p = yes (r-tabs p)
K ⊢alg ∀' a | no ¬p = no (λ{ (r-tabs x) → ¬p x })
