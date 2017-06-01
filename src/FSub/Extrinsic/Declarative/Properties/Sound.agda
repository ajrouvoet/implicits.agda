module FSub.Extrinsic.Declarative.Properties.Sound where

open import Prelude hiding (⊥; id)
open import Function as Fun using ()
open import Data.List hiding ([_]; monad)
open import Data.List.Properties as ListProp using ()
open import Data.Fin.Substitution
open import Extensions.List
open import Data.Maybe hiding (monad)

open import FSub.Types
open import FSub.Extrinsic.Declarative.Welltyped
open import FSub.Extrinsic.Declarative.Semantics

module UglyBits where

  {-}
  _wt/_ : ∀ {n m}{Γ : Ctx n}{N t a} → N , Γ ⊢ t ∶ a → (ρ : Sub Type n m) → N , (Γ ctx/ ρ) ⊢ t ∶ (a / ρ)
  unit wt/ ρ = unit
  ƛ a t wt/ ρ = ƛ (a / ρ) (t wt/ ρ)
  var x wt/ ρ = var ([]=-map x)
  (f · e) wt/ ρ = (f wt/ ρ) · (e wt/ ρ)
  Λ t wt/ ρ = Λ (subst (λ Γ → _ , Γ ⊢ _ ∶ _) (sym $ CtxLemmas.ctx/-wk-comm _ ρ) (t wt/ (ρ ↑)))
  (_[_] {a = a} t b) wt/ ρ =
    subst (λ a → _ , _ ⊢ _ ∶ a) (sym $ Lemmas.sub-commutes a) ((t wt/ ρ) [ (b / ρ) ])
  -}

open UglyBits
open import Data.Star

private
  -- use transitivity of subtyping as subsumption for values in the
  -- interpreter monad
  trans-ok : ∀ {n}{N : νCtx n}{x a aᵘ} →
            All (Any (λ v → N ⊢̬ v <: a)) x → N ⊢ a <: aᵘ →
            All (Any (λ v → N ⊢̬ v <: aᵘ)) x
  trans-ok (just² v<:a) q = just² {!!}
  trans-ok nothing q = nothing

_⊢_⇓_ok : ∀ {n N}{Γ : Ctx n}{μ : Env}{t a} →
          N , Γ ⊢ μ → N , Γ ⊢ t ∶ a → ∀ n →
          ------------------------------------------------------------
          All (Any (λ v → N ⊢̬ v <: a)) (μ ⊢ t ⇓ n)

E ⊢ t ⇓ zero ok = nothing

E ⊢ unit ⇓ suc n ok = just² (unit % ε)
E ⊢ ƛ a t ⇓ suc n ok = just² (clos t E % ε)
E ⊢ Λ u t ⇓ suc n ok = just² (tclos u E t % ε)

E ⊢ var x ⇓ suc n ok with pointwise-maybe-lookup E x
... | _ , is-just , p rewrite is-just = just² p

E ⊢ f · e ⇓ suc n ok
  with μ ⊢ (eraseᵗᵐ f) ⇓ n | μ ⊢ (eraseᵗᵐ e) ⇓ n | E ⊢ f ⇓ n ok | E ⊢ e ⇓ n ok
  where μ = (eraseᴱ E)
-- errors
... | nothing | _ | x | y = nothing
... | just _ | nothing | x | y = nothing
... | just nothing | _ | (just ()) | _
... | just (just _) | (just nothing) | _ | (just ())
-- success
... | just² x | just² y | just² (v∈l % l<:a⇒b) | just² (v∈k % k<:a) with Canonical.<:⇒ v∈l l<:a⇒b
E ⊢ f · e ⇓ suc n ok | just² _ | just² _ | just² (clos t Eclos % l<:a⇒b) | just² (v∈k % k<:a) | _ , _ , refl =
  trans-ok
    (((v∈k % <:-trans k<:a (<:-Lemmas.⇒-contra-dom l<:a⇒b)) ∷ Eclos) ⊢ t ⇓ n ok)
    (<:-Lemmas.⇒-cov-range l<:a⇒b)

E ⊢ t [ x ] ⇓ suc n ok with (eraseᴱ E) ⊢ (eraseᵗᵐ t) ⇓ n | E ⊢ t ⇓ n ok
... | nothing | _ = nothing
... | just nothing | just ()
... | just² _ | just² (v∈l % l<:∀a) with Canonical.<:∀≤ v∈l l<:∀a
E ⊢ t [ x ] ⇓ suc n ok | just² _ | just² (tclos u body Eclos % l<:∀) | _ , _ , refl = {!!}


E ⊢ subm t s ⇓ suc n ok = trans-ok (E ⊢ t ⇓ (suc n) ok) s
