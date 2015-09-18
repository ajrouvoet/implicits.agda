open import Prelude hiding (Bool)

module Implicits.Oliveira.Improved.Undecidable.Decidable (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Data.Fin.Substitution
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Types.Unification TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.Improved.Resolution TC _tc≟_
open import Extensions.ListFirst


mutual


    data _,_⊢_matches_ {ν} (ρs : List (Type ν)) : Fin (suc ν) → Type ν → SimpleType ν → Set where
        mtc-tabs : ∀ {r a α} → List.map tp-weaken ρs , suc α ⊢ r matches (stp-weaken a) →
                    ρs , α ⊢ ∀' r matches a
        mtc-iabs : ∀ {α a b c} → (a List.∷ ρs) , α ⊢ b matches c → ρs , α ⊢ a ⇒ b matches c
        mtc-simp : ∀ {α a b} → MGU α (simpl a) (simpl b) → ρs , α ⊢ (simpl a) matches b

    _⊢_match_ : ∀ {ν n} (K : Ktx ν n) → (a : Type ν) → (b : SimpleType ν) → Dec (K ⊢ a ↓ b)
    K ⊢ r match a = {!r!}

    _match1st_ : ∀ {ν n} (K : Ktx ν n) → (a : SimpleType ν) → Dec (∃ λ r → K ⟨ a ⟩= r)
    K match1st a = find (λ r → K ⊢ r ↓ a) (λ r → K ⊢ r match a) (proj₂ K)

    --
    --
    {-# NO_TERMINATION_CHECK #-}
    _⊢alg_ : ∀ {ν n} (K : Ktx ν n) → (a : Type ν) → Dec (K ⊢ᵣ a)
    K ⊢alg simpl x with K match1st x
    K ⊢alg simpl x | yes (r , p) = yes (r-simp p)
    K ⊢alg simpl x | no ¬p = no λ{ (r-simp p) → ¬p (, p) }
    K ⊢alg (a ⇒ b) with (a ∷K K) ⊢alg b
    K ⊢alg (a ⇒ b) | yes p = yes $ r-iabs a p
    K ⊢alg (a ⇒ b) | no ¬p = no (λ{ (r-iabs .a x) → ¬p x })
    K ⊢alg ∀' a with (ktx-weaken K) ⊢alg a
    K ⊢alg ∀' a | yes p = yes (r-tabs p)
    K ⊢alg ∀' a | no ¬p = no (λ{ (r-tabs x) → ¬p x })
