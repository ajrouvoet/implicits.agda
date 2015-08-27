open import Prelude

module Implicits.Oliveira.Deterministic.Decidable
  (TC : Set)
  (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Data.Fin.Substitution
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Types.Unification TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.Deterministic.Resolution TC _tc≟_
open import Extensions.ListFirst

data _,_⊢_matches_ {ν} (ρs : List (Type ν)) : Fin (suc ν) → Type ν → SimpleType ν → Set where
  mtc-tabs : ∀ {r a α} → List.map tp-weaken ρs , suc α ⊢ r matches (stp-weaken a) →
             ρs , α ⊢ ∀' r matches a
  mtc-iabs : ∀ {α a b c} → (a List.∷ ρs) , α ⊢ b matches c → ρs , α ⊢ a ⇒ b matches c
  mtc-simp : ∀ {α a b} → MGU α (simpl a) (simpl b) → ρs , α ⊢ (simpl a) matches b

_⊢match1st_ : ∀ {ν n} (K : Ktx ν n) → (a : SimpleType ν) → Set
K ⊢match1st a  = ∃ λ r → first r ∈ proj₂ K ⇔ (λ r' → List.[] , zero ⊢ r' matches a)

_match1st_ : ∀ {ν n} (K : Ktx ν n) → (a : SimpleType ν) → Dec (K ⊢match1st a)
(Γ , Δ) match1st a = find (λ r → List.[] , zero ⊢ r matches a) (match List.[] zero a) Δ

  where
    match : ∀ {ν} → (ρs : List (Type ν)) → (α : Fin (suc ν)) → (a : SimpleType ν) → (r : Type ν) →
            Dec (ρs , α ⊢ r matches a)
    match ρs α a (simpl x) with mgu α (simpl x) (simpl a)
    match ρs α a (simpl x) | yes mgu = yes (mtc-simp mgu)
    match ρs α a (simpl x) | no ¬p = no (λ{ (mtc-simp x) → ¬p x })
    match ρs α a (b ⇒ c) with match (b List.∷ ρs) α a c
    match ρs α a (b ⇒ c) | yes p = yes $ mtc-iabs p
    match ρs α a (b ⇒ c) | no ¬p = no (λ{ (mtc-iabs x) → ¬p x})
    match ρs α a (∀' r) with match (List.map tp-weaken ρs) (suc α) (stp-weaken a) r
    match ρs α a (∀' r) | yes p = yes $ mtc-tabs p
    match ρs α a (∀' r) | no ¬p = no (λ{ (mtc-tabs x) → ¬p x })

module Lemmas where

  lem-A3 : ∀ {ν n} (K : Ktx ν n) {a r} → K ⟨ a ⟩= r → r List.∈ (proj₂ K)
  lem-A3 _ = proj₁ ∘ first⟶∈

  lem-A6 : ∀ {ν} {ρs} {r : Type ν} {a α} → ρs , α ⊢ r matches a →
           ∃₂ λ a' (u : MGU α r a') → (apply-unifier α u r) ◁ a
  lem-A6 (mtc-tabs p) = {!!}
  lem-A6 (mtc-iabs p) = {!!}
  lem-A6 (mtc-simp {b = b} x) rewrite mgu-unifies x = simpl b , x , {!refl!}

  lem-A6' : ∀ {ν} ρs {r : Type ν} {a α} → r ◁ a → ρs , α ⊢ r matches a
  lem-A6' x = {!!}

  -- p'haps counterintuitively the following proposition is NOT a theorem:
  -- Δ⊢ᵣa⟶Δ≢Ø : ∀ {ν n} {K : Ktx ν n} {a} → K ⊢ᵣ a → ∃ λ b → b List.∈ (proj₂ K)
  -- since [] ⊢ᵣ Nat ⇒ Nat through the r-iabs rule, but also:
  -- [] ⊢ᵣ Nat ⇒ (Nat ⇒ Nat), etc; through recursion on r-iabs

  lem-A7 : ∀ {ν n} (K : Ktx ν n) {a} → K ⊢match1st a → ∃ λ r → K ⟨ a ⟩= r
  lem-A7 (Δ , .(r List.∷ v)) (r , here p v) = , here {!!} v
  lem-A7 (Δ , x List.∷ .ρs) (r , there {v = ρs} .x ¬px fst≡r) =
    , there
      x
      (λ x'◁a → ¬px (lem-A6' List.[] x'◁a))
      (proj₂ $ lem-A7 (Δ , ρs) (, fst≡r))

open Lemmas

{-# NO_TERMINATION_CHECK #-}
_⊢alg_ : ∀ {ν n} (K : Ktx ν n) → (a : Type ν) → Dec (K ⊢ᵣ a)
K ⊢alg simpl x with K match1st x
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
