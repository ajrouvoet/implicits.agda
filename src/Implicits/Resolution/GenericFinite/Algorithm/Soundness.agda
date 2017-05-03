open import Prelude

module Implicits.Resolution.GenericFinite.Algorithm.Soundness where

open import Induction.WellFounded
open import Induction.Nat
open import Data.List
open import Data.List.Any
open Membership-≡
open import Data.Fin.Substitution
open import Data.Nat.Base using (_<′_)
open import Data.Maybe as Maybe
open import Data.Nat hiding (_<_)
open import Data.Nat.Properties
open import Relation.Binary using (module DecTotalOrder)
open DecTotalOrder decTotalOrder using () renaming (refl to ≤-refl; trans to ≤-trans)

open import Implicits.Syntax
open import Implicits.Syntax.Type.Unification
open import Implicits.Syntax.Type.Unification.Lemmas as mgu hiding (sound)
open import Implicits.Substitutions
open import Implicits.Substitutions.Lemmas
open import Implicits.Resolution.GenericFinite.Resolution
open import Implicits.Resolution.GenericFinite.Algorithm
open import Implicits.Resolution.GenericFinite.TerminationCondition
open import Implicits.Resolution.Termination

open import Data.Vec hiding (_∈_)
open import Extensions.Bool as Bl

private
  module M = MetaTypeMetaSubst

module ResolutionSound (cond : TerminationCondition) where

  open TerminationCondition cond
  open ResolutionAlgorithm cond
  open ResolutionRules cond

  open Lemmas

  postulate lem₄ : ∀ {m ν} (a : MetaType m (suc ν)) u us →
                   from-meta ((M.open-meta a) M./ (us M.↑) M./ (M.sub u))
                     ≡ (from-meta (a M./ (us M.↑tp))) tp[/tp from-meta u ]

  open-↓-∀ : ∀ {ν m} {Δ : ICtx ν} {Φ} (a : MetaType m (suc ν)) τ u us →
        Δ , Φ ⊢ (from-meta ((open-meta a) M./ (u ∷ us))) ↓ τ →
        Δ , Φ ⊢ (from-meta (∀' a M./ us)) ↓ τ
  open-↓-∀ {Δ = Δ} {Φ = Φ} a τ u us p = (i-tabs (from-meta u) (subst (λ v → Δ , Φ ⊢ v ↓ τ) (begin
        from-meta (M._/_ (open-meta a) (u ∷ us))
          ≡⟨ cong (λ v → from-meta (M._/_ (open-meta a) v)) (sym $ us↑-⊙-sub-u≡u∷us u us) ⟩
        from-meta ((open-meta a) M./ (us M.↑ M.⊙ (M.sub u)))
          ≡⟨ cong from-meta (/-⊙ (open-meta a)) ⟩
        from-meta ((open-meta a) M./ us M.↑ M./ (M.sub u))
          ≡⟨ lem₄ a u us ⟩
        from-meta (M._/_ a (us M.↑tp)) tp[/tp from-meta u ] ∎) p))
      where open MetaTypeMetaLemmas hiding (subst)

  mutual
    match'-sound : ∀ {ν m} (Δ : ICtx ν) (Φ : TCtx) τ (r : MetaType m ν) →
                  (Φ↓ : T-Acc Φ) → (m↓ : m<-Acc r) →
                  Maybe.All (λ u → Δ , Φ ⊢ from-meta (r M./ u) ↓ τ) (match' Δ Φ τ r Φ↓ m↓)
    match'-sound Δ Φ τ (a ⇒ b) Φ↓ (acc m↓)
      with match'       Δ Φ τ b Φ↓ (m↓ _ (b-m<-a⇒b a b))
         | match'-sound Δ Φ τ b Φ↓ (m↓ _ (b-m<-a⇒b a b))
    match'-sound Δ Φ τ (a ⇒ b) Φ↓ (acc m↓) | just u | just pu
      with (step Φ Δ (from-meta (a M./ u)) (from-meta (b M./ u)) τ) <? Φ
    match'-sound Δ Φ τ (a ⇒ b) (acc Φ↓) (acc m↓) | just u | just pu | no Φ> = nothing
    match'-sound Δ Φ τ (a ⇒ b) (acc Φ↓) (acc m↓) | just u | just pu | yes Φ< 
      with resolve' Δ (step Φ Δ (from-meta (a M./ u)) (from-meta (b M./ u)) τ)
                    (from-meta (a M./ u)) (Φ↓ _ Φ<)
         | sound'   Δ (step Φ Δ (from-meta (a M./ u)) (from-meta (b M./ u)) τ)
                    (from-meta (a M./ u)) (Φ↓ _ Φ<) 
    match'-sound Δ Φ τ (a ⇒ b) (acc Φ↓) (acc m↓) | just u | just pu | yes Φ< | true | true px =
      just (i-iabs Φ< px pu) 
    match'-sound Δ Φ τ (a ⇒ b) (acc Φ↓) (acc m↓) | just u | just pu | yes Φ< | false | false = nothing 
    match'-sound Δ Φ τ (a ⇒ b) (acc Φ↓) (acc m↓) | nothing | _ = nothing
    match'-sound Δ Φ τ (∀' r) Φ↓ (acc m↓)
      with match'       Δ Φ τ (open-meta r) Φ↓ (m↓ _ (open-meta-a-m<-∀'a r))
         | match'-sound Δ Φ τ (open-meta r) Φ↓ (m↓ _ (open-meta-a-m<-∀'a r))
    match'-sound Δ Φ τ (∀' r) Φ↓ (acc m↓) | just (u ∷ us) | just px = just (open-↓-∀ r τ u us px)
    match'-sound Δ Φ τ (∀' r) Φ↓ (acc m↓) | nothing | nothing = nothing
    match'-sound Δ Φ τ (simpl x) Φ↓ m↓ with mgu (simpl x) τ | mgu.sound (simpl x) τ 
    match'-sound Δ Φ τ (simpl x) Φ↓ m↓ | just _ | just px =
      just (subst (λ z → Δ , Φ ⊢ z ↓ τ) (sym px) (i-simp τ))
    match'-sound Δ Φ τ (simpl x) Φ↓ m↓ | nothing | nothing = nothing

    match-sound : ∀ {ν} (Δ : ICtx ν) (Φ : TCtx) τ r → (Φ↓ : T-Acc Φ) → 
                  Bl.All (Δ , Φ ⊢ r ↓ τ) (match Δ Φ τ r Φ↓)
    match-sound Δ Φ τ r Φ↓ with
      match' Δ Φ τ (to-meta {zero} r) Φ↓ (m<-well-founded _) |
      match'-sound Δ Φ τ (to-meta {zero} r) Φ↓ (m<-well-founded _)
    match-sound Δ Φ τ r Φ↓ | just x | just px = true (subst (λ z → Δ , Φ ⊢ z ↓ τ) eq px)
      where
        eq : ∀ {ν} {a : Type ν} {s} → from-meta (to-meta {zero} a M./ s) ≡ a
        eq {a = a} {s = []} = begin
            from-meta (M._/_ (to-meta {zero} a) [])
          ≡⟨ cong (λ q → from-meta q) (MetaTypeMetaLemmas.id-vanishes (to-meta {zero} a)) ⟩
            from-meta (to-meta {zero} a)
          ≡⟨ to-meta-zero-vanishes ⟩
            a ∎
    match-sound Δ Φ τ r Φ↓ | nothing | q = false

    match1st-sound : ∀ {ν} (Δ : ICtx ν) (Φ : TCtx) (ρs : ICtx ν) → (τ : SimpleType ν) → (Φ↓ : T-Acc Φ) →
                    Bl.All (∃ λ r → (r ∈ ρs) × (Δ , Φ ⊢ r ↓ τ)) (match1st Δ Φ ρs τ Φ↓)
    match1st-sound Δ Φ [] τ Φ↓ = false
    match1st-sound Δ Φ (x ∷ ρs) τ Φ↓ with match Δ Φ τ x Φ↓ | match-sound Δ Φ τ x Φ↓
    match1st-sound Δ Φ (x ∷ ρs) τ Φ↓ | true | true px = true (x , (here refl , px)) 
    match1st-sound Δ Φ (x ∷ ρs) τ Φ↓ | false | false =
      all-map (match1st-sound Δ Φ ρs τ Φ↓) (λ{ (r , r∈ρs , r↓τ) → r , ((there r∈ρs) , r↓τ) })

    sound' : ∀ {ν} (Δ : ICtx ν) Φ r → (Φ↓ : T-Acc Φ) → Bl.All (Δ , Φ ⊢ᵣ r) (resolve' Δ Φ r Φ↓)
    sound' Δ Φ (simpl x) Φ↓ =
      all-map (match1st-sound Δ Φ Δ x Φ↓) (λ{ (r , r∈Δ , r↓τ) → r-simp r∈Δ r↓τ })
    sound' Δ Φ (a ⇒ b) Φ↓ = all-map (sound' (a ∷ Δ) Φ b Φ↓) (λ x → r-iabs a x)
    sound' Δ Φ (∀' r) Φ↓ = all-map (sound' (ictx-weaken Δ) Φ r Φ↓) r-tabs

    sound : ∀ {ν} (Δ : ICtx ν) r {Φ} → (Φ↓ : T-Acc Φ) → Bl.All (Δ , Φ ⊢ᵣ r) (resolve Δ Φ r)
    sound Δ r Φ↓ = sound' Δ _ r (wf-< _)
