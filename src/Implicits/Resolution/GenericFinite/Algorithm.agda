open import Prelude

module Implicits.Resolution.GenericFinite.Algorithm (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Induction.WellFounded
open import Induction.Nat
open import Data.Fin.Substitution
open import Data.Nat.Base using (_<′_)
open import Data.Maybe
open import Data.Nat hiding (_<_)
open import Data.Nat.Properties
open import Relation.Binary using (module DecTotalOrder)
open DecTotalOrder decTotalOrder using () renaming (refl to ≤-refl; trans to ≤-trans)

open import Implicits.Syntax TC _tc≟_
open import Implicits.Syntax.Type.Unification TC _tc≟_
open import Implicits.Substitutions TC _tc≟_
open import Implicits.Substitutions.Lemmas TC _tc≟_
open import Implicits.Resolution.GenericFinite.Resolution TC _tc≟_
open import Implicits.Resolution.GenericFinite.TerminationCondition
open import Implicits.Resolution.Termination TC _tc≟_

module M = MetaTypeMetaSubst

module Lemmas where
  m<-Acc : ∀ {m ν} → MetaType m ν → Set
  m<-Acc {m} {ν} r = Acc _m<_ (m , ν , r)

  ρ<-Acc : ∀ {ν} → Type ν → Set
  ρ<-Acc {ν} r = Acc _ρ<_ (ν , r)

  module Arg<-well-founded  where
    open Lexicographic (_N<_) (const _ρ<_)

    open import Induction.Nat
    open import Data.Nat.Properties
    module image = Subrelation {A = ℕ} {_N<_} {_<′_} ≤⇒≤′

    arg<-well-founded : Well-founded _<_
    arg<-well-founded = well-founded (image.well-founded <-well-founded) ρ<-well-founded

    _arg<_ = _<_

    -- Accessibility of the 'goal' type during resolution.
    -- Either the *head* of the goal shrinks (Oliveira's termination condition)
    -- Or the head size remains equal and the goal shrinks in an absolute sense.
    Arg<-Acc : ∀ {ν} → Type ν → Set
    Arg<-Acc a = Acc _arg<_ (h|| a || , (, a))

  open Arg<-well-founded using (Arg<-Acc; arg<-well-founded) public

open Lemmas

module ResolutionAlgorithm (cond : TerminationCondition) where
  open TerminationCondition cond
  open ResolutionRules cond

  mutual

    match' : ∀ {m ν} (Δ : ICtx ν) (Φ : TCtx) τ → (r : MetaType m ν) →
            T-Acc Φ →
            m<-Acc r →
            Maybe (Sub (flip MetaType ν) m zero)
    match' Δ Φ τ (simpl x) f g = mgu (simpl x) τ 

    match' Δ Φ τ (a ⇒ b) (acc f) (acc g) with match' Δ Φ τ b (acc f) (g _ (b-m<-a⇒b a b))
    match' Δ Φ τ (a ⇒ b) (acc f) (acc g) | nothing = nothing
    match' Δ Φ τ (a ⇒ b) (acc f) (acc g) | just u
      with (step Φ) <? Φ
    match' Δ Φ τ (a ⇒ b) (acc f) (acc g) | just u | yes Φ<
      with resolve' Δ (step Φ) (from-meta (a M./ u)) (f _ Φ<)
    match' Δ Φ τ (a ⇒ b) (acc f) (acc g) | just u | yes Φ< | true = just u
    match' Δ Φ τ (a ⇒ b) (acc f) (acc g) | just u | yes Φ< | false = nothing
    match' Δ Φ τ (a ⇒ b) (acc f) (acc g) | just u | no φ> = nothing

    match' Δ Φ τ (∀' a) f (acc g) with match' Δ Φ τ (open-meta a) f (g _ (open-meta-a-m<-∀'a a))
    match' Δ Φ τ (∀' a) f (acc g) | just p = just (Prelude.tail p)
    match' Δ Φ τ (∀' r) f (acc g) | nothing = nothing

    -- match defers to match', which concerns itself with MetaTypes.
    -- If match' finds a match, we can use the fact that we have zero unification variables open here
    -- to show that we found the right thing.
    match : ∀ {ν} (Δ : ICtx ν) (Φ : TCtx) τ r → T-Acc Φ → Bool
    match Δ Φ τ a f = is-just (match' Δ Φ τ (to-meta {zero} a) f (m<-well-founded _))

    match1st : ∀ {ν} (Δ : ICtx ν) (Φ : TCtx) (ρs : ICtx ν) → (τ : SimpleType ν) → T-Acc Φ → Bool
    match1st Δ Φ List.[] τ Φ↓ = false
    match1st Δ Φ (x List.∷ xs) τ Φ↓ with match Δ Φ τ x Φ↓
    match1st Δ Φ (x List.∷ xs) τ Φ↓ | true = true
    match1st Δ Φ (x List.∷ xs) τ Φ↓ | false with match1st Δ Φ xs τ Φ↓
    match1st Δ Φ (x List.∷ xs) τ Φ↓ | false | true = true
    match1st Δ Φ (x List.∷ xs) τ Φ↓ | false | false = false

    resolve' : ∀ {ν} (Δ : ICtx ν) (Φ : TCtx) r → T-Acc Φ → Bool
    resolve' Δ Φ (simpl x) Φ↓ = match1st Δ Φ Δ x Φ↓
    resolve' Δ Φ (a ⇒ b) Φ↓ = resolve' (a List.∷ Δ) Φ b Φ↓ 
    resolve' Δ Φ (∀' r) Φ↓ = resolve' (ictx-weaken Δ) Φ r Φ↓

    resolve : ∀ {ν} (Δ : ICtx ν) (Φ : TCtx) r → Bool
    resolve Δ Φ r = resolve' Δ Φ r (wf-< Φ)
