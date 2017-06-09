module SystemF.BigStep.Extrinsic.Properties.Sound where

open import Prelude hiding (⊥; id)
open import Function as Fun using ()
open import Data.List hiding ([_]; monad)
open import Data.List.Properties as ListProp using ()
open import Data.Fin.Substitution
open import Extensions.List
open import Data.Maybe hiding (monad)

open import SystemF.BigStep.Types
open import SystemF.BigStep.Extrinsic.Terms
open import SystemF.BigStep.Extrinsic.Welltyped

open import SystemF.BigStep.Extrinsic.Semantics

module FunctionalOk where
  open Functional

  -- extrinsic safety
  _⊢_⇓_ok : ∀ {n}{Γ : Ctx n}{μ : Env}{t a} →
            Γ ⊢ μ → Γ ⊢ t ∶ a → ∀ n → All (Any (λ v → ⊢̬ v ∶ a)) (μ ⊢ t ⇓ n)

  μ ⊢ x ⇓ zero ok = nothing

  μ ⊢ unit ⇓ suc n ok = just² unit

  μ ⊢ ƛ a x ⇓ suc n ok = just² (clos x μ)

  μ ⊢ Λ x ⇓ suc n ok = just² (tclos x μ)

  _⊢_⇓_ok {μ = E} μ (_·_ {f = f}{e = e} wtf wte) (suc n) with
    E ⊢ f ⇓ n | E ⊢ e ⇓ n | μ ⊢ wtf ⇓ n ok | μ ⊢ wte ⇓ n ok
  -- timeout
  ... | nothing | _ | _ | _ = nothing
  ... | just _ | nothing | _ | _ = nothing
  -- success
  ... | just² (clos μ' t) | just² v | just² (clos wtt wtμ') | just² px = (px ∷ wtμ') ⊢ wtt ⇓ n ok
  -- semantic error propagation
  ... | just nothing | _ | (just ()) | _
  ... | _ | just nothing | _ | (just ())
  -- semantic errors
  ... | just² (tclos _ _) | _ | just² () | _
  ... | just² unit | _ | just² () | _

  _⊢_⇓_ok {μ = E} μ (_[_] {f = f} wtf b) (suc n) with E ⊢ f ⇓ n | μ ⊢ wtf ⇓ n ok
  -- timeout
  ... | nothing | _ = nothing
  -- semantic errors
  ... | just nothing | (just ())
  ... | just² unit | just² ()
  ... | just² (clos x t) | just² ()
  -- success
  ... | just² (tclos μ' t) | just² (tclos tok μ'ok) =
    μ'ok ⊢ subst (λ Γ → Γ ⊢ _ ∶ _) (CtxLemmas.ctx/-wk-sub≡id _ b) (tok wt/ (sub b)) ⇓ n ok

  μ ⊢ var x ⇓ suc n ok with pointwise-maybe-lookup μ x
  μ ⊢ var x ⇓ suc n ok | _ , is-just , p rewrite is-just = just² p

module RelationalOk where

  open import Coinduction
  open import Category.Monad.Partiality
  open Workaround

  open Relational

  preservation : ∀ {n}{Γ : Ctx n}{μ : Env}{t a v} → Γ ⊢ μ → Γ ⊢ t ∶ a → μ ⊢ t ⇓ v → ⊢̬ v ∶ a
  preservation E unit unit⇓ = unit
  preservation E (ƛ a p) λ⇓ = clos p E
  preservation E (Λ p) Λ⇓ = tclos p E
  preservation E (f · e) (app⇓ f⇓clos e⇓v body⇓) with preservation E f f⇓clos | preservation E e e⇓v
  ... | clos body Eclos | z = preservation (z ∷ Eclos) body body⇓
  preservation E (p [ b ]) (t[]⇓ p⇓tclos body⇓) with preservation E p p⇓tclos
  ... | tclos body Eclos =
    preservation
      (subst (flip _⊢_ _) (sym $ CtxLemmas.ctx/-wk-sub≡id _ b) Eclos)
      (body wt/ (sub b))
      body⇓
  preservation E (var p) (var⇓ q) = pointwise-lookup′ E p q

  -- soundness
  _⊢_⇓ok : ∀ {n}{Γ : Ctx n}{μ : Env}{t a} → Γ ⊢ μ → Γ ⊢ t ∶ a → (∃ λ v → μ ⊢ t ⇓ v) ⊥P
  E ⊢ unit ⇓ok = now (unit , unit⇓)
  E ⊢ ƛ a t₁ ⇓ok = now (clos _ _ , λ⇓)
  E ⊢ Λ t₁ ⇓ok = now (tclos _ _ , Λ⇓)
  E ⊢ var x ⇓ok with pointwise-lookup E x
  E ⊢ var x ⇓ok | v , p , v∶a = now (v , var⇓ p)
  _⊢_⇓ok {Γ = Γ} {μ = μ} E (f · e) = E ⊢ f ⇓ok >>= (
    λ fv → E ⊢ e ⇓ok >>= (
    λ v →
      eval-body f (proj₂ fv) e (proj₂ v)
    ))
    where
      eval-body : ∀ {a b f e fv v} →
        Γ ⊢ f ∶ (a ⇒ b) → μ ⊢ f ⇓ fv →
        Γ ⊢ e ∶ a → μ ⊢ e ⇓ v →
        (∃ λ r → μ ⊢ f · e ⇓ r) ⊥P
      eval-body f f⇓ e e⇓ with preservation E f f⇓ | preservation E e e⇓
      eval-body f f⇓ e e⇓ | clos body Eclos | wtv =
        later (♯ (((wtv ∷ Eclos) ⊢ body ⇓ok) >>= λ{ (r , body⇓) → now (r , app⇓ f⇓ e⇓ body⇓)}))
  E ⊢ t [ b ] ⇓ok = {!!}
