open import Prelude

module Implicits.Resolution.GenericFinite.Resolution where

open import Coinduction
open import Data.Fin.Substitution
open import Relation.Binary using (Rel)

open import Implicits.Syntax
open import Implicits.Syntax.Type.Unification
open import Implicits.Substitutions
open import Implicits.Substitutions.Lemmas.MetaType
open import Implicits.Resolution.Termination
open import Implicits.Resolution.GenericFinite.TerminationCondition

private
  module M = MetaTypeMetaSubst

module ResolutionRules (cond : TerminationCondition) where
  open TerminationCondition cond

  mutual
    data _,_⊢_↓_ {ν} (Δ : ICtx ν) : (Φ : TCtx) → Type ν → SimpleType ν → Set where
      i-simp : ∀ {Φ} a → Δ , Φ ⊢ simpl a ↓ a
      i-iabs : ∀ {Φ ρ₁ ρ₂ a} → let Φ' = (step Φ Δ ρ₁ ρ₂ a) in
               Φ' < Φ → Δ , Φ' ⊢ᵣ ρ₁ → Δ , Φ ⊢ ρ₂ ↓ a → Δ , Φ ⊢ ρ₁ ⇒ ρ₂ ↓ a
      i-tabs : ∀ {Φ ρ a} b → Δ , Φ ⊢ ρ tp[/tp b ] ↓ a → Δ , Φ ⊢ ∀' ρ ↓ a

    data _,_⊢ᵣ_ {ν} (Δ : ICtx ν) : TCtx → Type ν → Set where
      r-simp : ∀ {Φ r τ} → r List.∈ Δ → Δ , Φ ⊢ r ↓ τ → Δ , Φ ⊢ᵣ simpl τ
      r-iabs : ∀ {Φ} ρ₁ {ρ₂} → ((ρ₁ List.∷ Δ) , Φ ⊢ᵣ ρ₂) → Δ , Φ ⊢ᵣ (ρ₁ ⇒ ρ₂)
      r-tabs : ∀ {Φ ρ} → ictx-weaken Δ , Φ ⊢ᵣ ρ → Δ , Φ ⊢ᵣ ∀' ρ

  {-
  postulate ↓-◁-unifiable : ∀ {ν} {Δ : ICtx ν} {Φ} {r τ} → Δ , Φ ⊢ r ↓ τ →
                            ◁-Unifiable (to-meta {zero} r) τ
  ↓-◁-unifiable (i-simp τ) = mgu-id τ
  ↓-◁-unifiable (i-iabs _ _ p) = ↓-◁-unifiable p
  ↓-◁-unifiable (i-tabs {ρ = a} b p) = {!!} -- lem a b (↓-◁-unifiable p)
    where
  
      lema :  ∀ {ν m} (a : MetaType m (suc ν)) b {τ} →
              ◁-Unifiable ((open-meta a) M./ M.sub b) τ → ◁-Unifiable (open-meta a) τ
      lema x = {!!}

      -- (a tp[/tp b]) ◁m ≡ (open-meta a M./ M.sub b) ◁m
      -- implies: ((open-meta a M./ M.sub b) ◁m) / u ≡ τ
      -- ((x / sub b) ◁m) / u ≡ (x ◁m) / sub b / u ≡ (x ◁m) / (b ∷ u)
      -- subst: ((open-meta a) ◁m) / (b ∷ u) ≡ τ
      -- ((open-meta a) ◁m) ≡ ((∀' a) ◁m)
      -- subst: ((∀' a) ◁m) / (b ∷ u) ≡ τ
      -- implies: ◁-Unifiable (∀' m) τ
      lem : ∀ {ν} (a : Type (suc ν)) b {τ} →
                      ◁-Unifiable (to-meta {zero} (a tp[/tp b ])) τ →
                      ◁-Unifiable (to-meta {zero} (∀' a)) τ
      lem a b {τ} (u , a/u≡b) = {!, proj₂ r!}
        where
          q : ◁-Unifiable ((open-meta $ to-meta {zero} a) M./ M.sub (to-meta b)) τ
          q = subst (λ z → ◁-Unifiable z τ) (MetaTypeMetaLemmas.lem₁ a b) (, a/u≡b)
          r : Unifiable ((open-meta $ to-meta {zero} a) M.◁m) τ
          r = lema (to-meta {zero} a) (to-meta {zero} b) q
          z : ∀ {ν} {u : Type (suc ν)} → ((to-meta {zero} (∀' u)) M.◁m) ≡ ((open-meta (to-meta {zero} u)) M.◁m)
          z = refl
      -}
