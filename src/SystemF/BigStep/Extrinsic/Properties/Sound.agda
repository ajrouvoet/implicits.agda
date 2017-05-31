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

module UglyBits where

  _wt/_ : ∀ {n m}{Γ : Ctx n}{t a} → Γ ⊢ t ∶ a → (ρ : Sub Type n m) → (Γ ctx/ ρ) ⊢ t ∶ (a / ρ)
  unit wt/ ρ = unit
  ƛ a t wt/ ρ = ƛ (a / ρ) (t wt/ ρ)
  var x wt/ ρ = var ([]=-map x)
  (f · e) wt/ ρ = (f wt/ ρ) · (e wt/ ρ)
  Λ t wt/ ρ = Λ (subst (λ Γ → Γ ⊢ _ ∶ _) (sym $ CtxLemmas.ctx/-wk-comm _ ρ) (t wt/ (ρ ↑)))
  (_[_] {a = a} t b) wt/ ρ =
    subst (λ a → _ ⊢ _ ∶ a) (sym $ Lemmas.sub-commutes a) ((t wt/ ρ) [ (b / ρ) ])

open UglyBits

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
