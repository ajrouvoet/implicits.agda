module Implicits.Resolution.Infinite.NormalFormEquiv where

open import Prelude

open import Implicits.Syntax
open import Implicits.Resolution.Infinite.Resolution
open import Implicits.Resolution.Embedding
open import Implicits.Resolution.Embedding.Lemmas

open import SystemF.Everything as F using ()
open import SystemF.NormalForm

open import Data.Vec hiding ([_])
open import Relation.Binary.HeterogeneousEquality as H using ()
open import Data.List.Any
open import Data.List.Properties
open import Data.Vec.Properties as VP using ()
open import Extensions.Vec
open import Function.Equivalence using (_⇔_; equivalence)

mutual

  from-⇓ : ∀ {ν n t a τ} {Γ : F.Ctx ν n} → Γ ⊢ t ⇓ a → ⟦ Γ ⟧ctx← ⊢ ⟦ a ⟧tp← ↓ τ →
           ∃ λ i → ⟦ Γ ⟧ctx← ⊢ ⟦ lookup i Γ ⟧tp← ↓ τ
  from-⇓ {Γ = Γ} (nvar i) ↓τ = i , ↓τ
  from-⇓ (napp p x) ↓τ = from-⇓ p (i-iabs (from-⇑ x) ↓τ)
  from-⇓ {Γ = Γ} (ntapp {a = a} b p) ↓τ = from-⇓ p
    (i-tabs ⟦ b ⟧tp← (subst (λ z → ⟦ Γ ⟧ctx← ⊢ z ↓ _) (⟦a/sub⟧tp← a b) ↓τ))

  from-⇑ : ∀ {ν n t a} {Γ : F.Ctx ν n} → Γ ⊢ t ⇑ a → ⟦ Γ ⟧ctx← ⊢ᵣ ⟦ a ⟧tp←
  from-⇑ (nbase b x) with ⟦base⟧tp← b
  from-⇑ (nbase b x) | τ , eq with from-⇓ x (subst (λ z → _ ⊢ z ↓ τ) (sym $ eq) (i-simp τ))
  from-⇑ (nbase b x) | τ , eq | i , lookup-i↓tc =
    subst (λ z → _ ⊢ᵣ z) (sym $ eq) (r-simp (lookup-∈ i _) lookup-i↓tc)
  from-⇑ (nabs p) = r-iabs (from-⇑ p)
  from-⇑ (ntabs p) = r-tabs (subst (λ z → z ⊢ᵣ _) (⟦weaken⟧ctx← _) (from-⇑ p))

  to-⇓ : ∀ {ν} {Δ : ICtx ν} {a τ t₁} → Δ ⊢ a ↓ τ → ⟦ Δ ⟧ctx→ ⊢ t₁ ⇓ ⟦ a ⟧tp→ →
        ∃ λ t₂ → ⟦ Δ ⟧ctx→ ⊢ t₂ ⇓ ⟦ simpl τ ⟧tp→
  to-⇓ (i-simp a) q = , q
  to-⇓ (i-iabs x p) q = to-⇓ p (napp q (proj₂ $ to-⇑ x))
  to-⇓ {Δ = Δ} (i-tabs {ρ = a} b p) q =
    to-⇓ p (subst (λ z → ⟦ Δ ⟧ctx→ ⊢ _ ⇓ z) (sym $ ⟦a/sub⟧tp→ a b) (ntapp ⟦ b ⟧tp→ q))

  to-⇑ : ∀ {ν} {Δ : ICtx ν} {a} → Δ ⊢ᵣ a → ∃ λ t → ⟦ Δ ⟧ctx→ ⊢ t ⇑ ⟦ a ⟧tp→
  to-⇑ {Δ = Δ} (r-simp {r = a} r r↓τ) = , nbase (⟦simpl⟧tp→ _) (proj₂ $ to-⇓ r↓τ var⇓a)
    where
      var⇓a : ⟦ Δ ⟧ctx→ ⊢ _ ⇓ ⟦ a ⟧tp→
      var⇓a = let (i , eq) = ∈⟶index (VP.List-∈⇒∈ r) in
        let i' = (subst Fin (sym $ length-map _ Δ) i) in
          subst (λ z → ⟦ Δ ⟧ctx→ ⊢ (F.var i') ⇓ z) (lookup⟦⟧ Δ i eq) (nvar i')
  to-⇑ (r-iabs p) =
    , nabs (proj₂ $ to-⇑ p)
  to-⇑ {Δ = Δ} (r-tabs {ρ = a} p) =
    , ntabs (⇑-subst-n (length-weaken-Δ Δ) (H.sym $ ⟦weaken⟧ctx→ Δ) (proj₂ (to-⇑ p)))

-- System F η-long-β-normal forms are isomorphic to infinite resolution derivations
equivalent : ∀ {ν} (Δ : ICtx ν) r → Δ ⊢ᵣ r ⇔ (∃ λ t → ⟦ Δ ⟧ctx→ ⊢ t ⇑ ⟦ r ⟧tp→)
equivalent Δ r = equivalence
  (λ x → to-⇑ x)
  (λ x → subst₂ (λ Δ' r' → Δ' ⊢ᵣ r') (ctx→← _) (tp→← r) (from-⇑ (proj₂ x)))


{-}
open import Function.Inverse
open import Function.Equality

-- from-⇑ : ∀ {ν n t a} {Γ : F.Ctx ν n} → Γ ⊢ t ⇑ a → ⟦ Γ ⟧ctx← ⊢ᵣ ⟦ a ⟧tp←
from-⇑' : ∀ {ν a} {Δ : ICtx ν} → (∃ λ t → ⟦ Δ ⟧ctx→ ⊢ t ⇑ ⟦ a ⟧tp→) → Δ ⊢ᵣ a
from-⇑' (_ , p) = subst₂ (λ Δ a → Δ ⊢ᵣ a) (ctx→← _) (tp→← _) (from-⇑ p)

-- from-⇓' : ∀ {ν a} {Δ : ICtx ν} {τ} → (∃ λ t → ⟦ Δ ⟧ctx→ ⊢ t ⇓ ⟦ a ⟧tp→) → Δ ⊢ Δ ⊢ a ↓ τ
-- from-⇓' {τ = τ} (_ , p) = subst₂ (λ Δ a → Δ ⊢ a ↓ τ) (ctx→← _) (tp→← _) (from-⇓ p)

-- from-to-⇓ : ∀ {ν a} {Δ : ICtx ν} {τ} → (p : Δ ⊢ a ↓ τ) → from-⇓' (to-⇓ p) ≡ p
-- from-to-⇓ p = ?

from-to-⇑ : ∀ {ν a} {Δ : ICtx ν} → (p : Δ ⊢ᵣ a) → from-⇑' (to-⇑ p) ≡ p
from-to-⇑ (r-simp x x₁) = {!!}
from-to-⇑ (r-iabs p) = begin
  from-⇑' (, (nabs (proj₂ (to-⇑ p))))
    ≡⟨ refl ⟩
  subst₂ (λ Δ a → Δ ⊢ᵣ a) (ctx→← _) (tp→← _) (from-⇑ (nabs (proj₂ (to-⇑ p))))
    ≡⟨ refl ⟩
  subst₂ (λ Δ a → Δ ⊢ᵣ a) (ctx→← _) (tp→← _) (r-iabs (from-⇑ (proj₂ (to-⇑ p))))
    ≡⟨ {!!} ⟩
  r-iabs (subst₂ (λ Δ a → Δ ⊢ᵣ a) (ctx→← _) (tp→← _) (from-⇑ (proj₂ (to-⇑ p))))
    ≡⟨ refl ⟩
  r-iabs (from-⇑' (to-⇑ p))
    ≡⟨ Prelude.cong r-iabs (from-to-⇑ p) ⟩
  r-iabs p ∎
from-to-⇑ (r-tabs p) with from-to-⇑ p
from-to-⇑ (r-tabs p) | x = {!x!}
  where
    lem : ∀ {ν a} {Δ : ICtx ν} →

to-from-⇑ : ∀ {ν a} {Δ : ICtx ν} → (p : ∃ λ t → ⟦ Δ ⟧ctx→ ⊢ t ⇑ ⟦ a ⟧tp→) → to-⇑ (from-⇑' p) ≡ p
to-from-⇑ p = {!!}

iso' : ∀ {ν a} {Δ : ICtx ν} → (→-to-⟶ (to-⇑ {Δ = Δ} {a = a})) InverseOf (→-to-⟶ from-⇑')
iso' = record { left-inverse-of = to-from-⇑; right-inverse-of = from-to-⇑ }
-}
