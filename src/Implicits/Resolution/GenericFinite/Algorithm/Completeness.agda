open import Prelude

module Implicits.Resolution.GenericFinite.Algorithm.Completeness where

open import Induction.WellFounded
open import Induction.Nat
open import Data.Fin.Substitution
open import Data.Nat.Base using (_<′_)
open import Data.Maybe as Maybe
open import Data.Nat hiding (_<_)
open import Data.Nat.Properties
open import Relation.Binary using (module DecTotalOrder)
open DecTotalOrder decTotalOrder using () renaming (refl to ≤-refl; trans to ≤-trans)
open import Data.Unit

open import Implicits.Syntax
open import Implicits.Syntax.Type.Unification
open import Implicits.Syntax.Type.Unification.Lemmas as mgu hiding (complete)
open import Implicits.Substitutions
open import Implicits.Substitutions.Lemmas
open import Implicits.Resolution.GenericFinite.Resolution
open import Implicits.Resolution.GenericFinite.Algorithm
open import Implicits.Resolution.GenericFinite.TerminationCondition
open import Implicits.Resolution.Termination

open import Extensions.Bool as Bool

private
  module M = MetaTypeMetaSubst

module ResolutionComplete (cond : TerminationCondition) where

  open TerminationCondition cond
  open ResolutionAlgorithm cond
  open ResolutionRules cond

  open Lemmas

  lemx : ∀ {ν m} {Δ : ICtx ν} {Φ} r c τ (u : M.MetaSub MetaType ν m zero) →
        Δ , Φ ⊢ from-meta (r M./ u M.↑tp) tp[/tp c ] ↓ τ →
        Δ , Φ ⊢ from-meta (open-meta r M./ (to-meta c ∷ u)) ↓ τ
  lemx r c τ u p = {!!}

  mutual
    match'-complete : ∀ {ν m} (Δ : ICtx ν) (Φ : TCtx) τ (r : MetaType m ν) →
                  (Φ↓ : T-Acc Φ) → (m↓ : m<-Acc r) →
                  (∃ λ u → Δ , Φ ⊢ from-meta (r M./ u) ↓ τ) →
                  Is-just (match' Δ Φ τ r Φ↓ m↓)

    match'-complete Δ Φ τ (a ⇒ b) f (acc g) (proj₁ , i-iabs x y b↓τ)
      with match' Δ Φ τ b f (g _ (b-m<-a⇒b a b))
         | match'-complete Δ Φ τ b f (g _ (b-m<-a⇒b a b)) (, b↓τ)
    match'-complete Δ Φ τ (a ⇒ b) f (acc g) (u , i-iabs x y b↓τ) | nothing | ()
    match'-complete Δ Φ τ (a ⇒ b) f (acc g) (u , i-iabs x₁ y b↓τ) | just u' | just px
      with (step Φ Δ (from-meta (a M./ u)) (from-meta (b M./ u)) τ) <? Φ
    match'-complete Δ Φ τ (a ⇒ b) f (acc g) (u , i-iabs x₁ y b↓τ) | just u' | just px | yes p = {!!}
    match'-complete Δ Φ τ (a ⇒ b) f (acc g) (u , i-iabs x₁ y b↓τ) | just u' | just px | no ¬p = {!x₁!}
    -- match'-complete Δ Φ τ (a ⇒ b) (acc f) (acc g) | just u | yes Φ<
      -- with resolve' Δ (step Φ Δ (from-meta (a M./ u)) (from-meta (b M./ u)) τ)
                    -- (from-meta (a M./ u)) (f _ Φ<)
    -- match'-complete Δ Φ τ (a ⇒ b) (acc f) (acc g) | just u | yes Φ< | true = just u
    -- match'-complete Δ Φ τ (a ⇒ b) (acc f) (acc g) | just u | yes Φ< | false = nothing
    -- match'-complete Δ Φ τ (a ⇒ b) (acc f) (acc g) | just u | no φ> = nothing

    match'-complete Δ Φ τ (∀' r) Φ↓ (acc m↓) (u , i-tabs b open-r↓τ)
      with match'          Δ Φ τ (open-meta r) Φ↓ (m↓ _ (open-meta-a-m<-∀'a r))
         | match'-complete Δ Φ τ (open-meta r) Φ↓ (m↓ _ (open-meta-a-m<-∀'a r))
                           (, lemx r b τ u open-r↓τ)
    match'-complete Δ Φ τ (∀' r) Φ↓ (acc m↓) (u , i-tabs b open-r↓τ) | just x | just px = just tt
    match'-complete Δ Φ τ (∀' r) Φ↓ (acc m↓) (u , i-tabs b open-r↓τ) | nothing | ()
    match'-complete Δ Φ .(tvar x) (simpl (tvar x)) Φ↓ m↓ (u , i-simp .(tvar x)) =
      mgu.complete (simpl (tvar x)) (tvar x) u refl
    match'-complete Δ Φ τ (simpl (mvar x)) Φ↓ m↓ (u , proj₂) = 
      let (u' , u'-uni) = mvar-unifiable x τ in mgu.complete (simpl (mvar x)) τ u' u'-uni
    match'-complete Δ Φ ._ (simpl (a →' b)) Φ↓ m↓ (u , i-simp ._) =
      mgu.complete (simpl (a →' b)) _ u refl
    match'-complete Δ Φ .(tc x) (simpl (tc x)) Φ↓ m↓ (u , ResolutionRules.i-simp .(tc x)) =
      mgu.complete (simpl (tc x)) _ u refl

    match-complete : ∀ {ν} (Δ : ICtx ν) (Φ : TCtx) → (τ : SimpleType ν) → (r : Type ν) →
                     (Φ↓ : T-Acc Φ) →
                     Δ , Φ ⊢ r ↓ τ →
                     Is-true (match Δ Φ τ r Φ↓)
    match-complete Δ Φ τ r Φ↓ p
      with match'          Δ Φ τ (to-meta {zero} r) Φ↓ (m<-well-founded _) 
         | match'-complete Δ Φ τ (to-meta {zero} r) Φ↓ (m<-well-founded _)
                           ([] , subst (λ z → Δ , Φ ⊢ z ↓ τ) (sym $ from-to-meta-/-vanishes) p)
    match-complete Δ Φ τ r Φ↓ p | just x | just px = true tt
    match-complete Δ Φ τ r Φ↓ p | nothing | ()

    match1st-complete : ∀ {ν} (Δ : ICtx ν) (Φ : TCtx) (ρs : ICtx ν) → (τ : SimpleType ν) →
                        (Φ↓ : T-Acc Φ) →
                        (∃ λ r → r List.∈ ρs × Δ , Φ ⊢ r ↓ τ) →
                        Is-true (match1st Δ Φ ρs τ Φ↓)
    match1st-complete Δ Φ List.[] τ Φ↓ (_ , () , _)
    match1st-complete Δ Φ (x List.∷ ρs) τ Φ↓ (.x , here refl , r↓τ)
      with match            Δ Φ τ x Φ↓
         | match-complete   Δ Φ τ x Φ↓ r↓τ
    match1st-complete Δ Φ (x List.∷ ρs) τ Φ↓ (.x , here refl , r↓τ) | true | true _ = true tt
    match1st-complete Δ Φ (x List.∷ ρs) τ Φ↓ (.x , here refl , r↓τ) | false | ()
    match1st-complete Δ Φ (x List.∷ ρs) τ Φ↓ (proj₁ , there p , r↓τ) with match Δ Φ τ x Φ↓
    match1st-complete Δ Φ (x List.∷ ρs) τ Φ↓ (r , there r∈ρs , r↓τ) | true  = true tt
    match1st-complete Δ Φ (x List.∷ ρs) τ Φ↓ (r , there r∈ρs , r↓τ) | false =
      match1st-complete Δ Φ ρs τ Φ↓ (r , r∈ρs , r↓τ)

    complete' : ∀ {ν} (Δ : ICtx ν) Φ {r} → (Φ↓ : T-Acc Φ) → Δ , Φ ⊢ᵣ r → Is-true (resolve' Δ Φ r Φ↓)
    complete' Δ Φ Φ↓ (r-simp x∈Δ x↓τ) = match1st-complete Δ Φ Δ _ Φ↓ (_ , x∈Δ , x↓τ)
    complete' Δ Φ Φ↓ (r-iabs ρ₁ p) = complete' (ρ₁ List.∷ Δ) Φ Φ↓ p
    complete' Δ Φ Φ↓ (r-tabs p) = complete' (ictx-weaken Δ) Φ Φ↓ p

    complete : ∀ {ν} (Δ : ICtx ν) Φ {r} → (Φ↓ : T-Acc Φ) → Δ , Φ ⊢ᵣ r → Is-true (resolve Δ Φ r)
    complete Δ Φ Φ↓ p = complete' Δ Φ (wf-< _) p
