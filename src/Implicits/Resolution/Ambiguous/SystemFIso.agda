module Implicits.Resolution.Ambiguous.SystemFIso where

open import Prelude

open import Function.Equivalence using (_⇔_; equivalence)
open import Data.List.Properties
open import Relation.Binary.HeterogeneousEquality as H using ()
open import Data.Vec.Properties as VP using ()

open import Implicits.Syntax
open import Implicits.Resolution.Ambiguous.Resolution
open import Implicits.Resolution.Ambiguous.Semantics
open import Implicits.Resolution.Embedding
open import Implicits.Resolution.Embedding.Lemmas

open import SystemF as F using ()

⟦_⟧term→ : ∀ {ν} {Δ : ICtx ν} {r} → Δ ⊢ᵣ r → F.Term ν (List.length (List.map ⟦_⟧tp→ Δ))
⟦_⟧term→ {ν} {Δ} (r-tabs x) = F.Λ (subst (F.Term (suc ν)) (length-weaken-Δ Δ) ⟦ x ⟧term→)
⟦ r-tapp a x ⟧term→ = ⟦ x ⟧term→ F.[ ⟦ a ⟧tp→ ]
⟦_⟧term→ {Δ = Δ} (r-ivar x) =
  F.var (subst Fin (sym $ length-map _ Δ) (proj₁ $ ∈⟶index (VP.List-∈⇒∈ x)))
⟦ r-iabs {a = a} x ⟧term→ = F.λ' ⟦ a ⟧tp→ ⟦ x ⟧term→
⟦ r-iapp f e ⟧term→ = ⟦ f ⟧term→ F.· ⟦ e ⟧term→

from-⊢ : ∀ {ν n t a} {Γ : F.Ctx ν n} → Γ F.⊢ t ∈ a → ⟦ Γ ⟧ctx← ⊢ᵣ ⟦ a ⟧tp←
from-⊢ (F.var x) = r-ivar (lookup-∈ x _)
from-⊢ {Γ = Γ} (F.Λ x) = r-tabs (subst (λ u → u ⊢ᵣ _) (⟦weaken⟧ctx← Γ) (from-⊢ x))
from-⊢ (F.λ' {b = b} a x) = r-iabs (from-⊢ x)
from-⊢ {Γ = Γ} (F._[_] {a = a} x b) = subst
  (λ u → ⟦ Γ ⟧ctx← ⊢ᵣ u)
  (sym (⟦a/sub⟧tp← a b))
  (r-tapp ⟦ b ⟧tp← (from-⊢ x))
from-⊢ (a F.· b) = r-iapp (from-⊢ a) (from-⊢ b)

to-⊢ : ∀ {ν} {Δ : ICtx ν} {r} → (p : Δ ⊢ᵣ r) → ⟦ Δ ⟧ctx→ F.⊢ ⟦ p ⟧term→ ∈ ⟦ r ⟧tp→
to-⊢ {Δ = Δ} (r-tabs {r = r} p) with to-⊢ p
to-⊢ {Δ = Δ} (r-tabs {r = r} p) | x =
  F.Λ (⊢subst-n (length-weaken-Δ Δ) (H.sym (⟦weaken⟧ctx→ Δ)) x)
to-⊢ (r-tapp a p) with to-⊢ p
to-⊢ {Δ = Δ} (r-tapp {r = a} b p) | x =
  subst
    (λ u → ⟦ Δ ⟧ctx→ F.⊢ ⟦ p ⟧term→ F.[ ⟦ b ⟧tp→ ] ∈ u)
    (sym $ ⟦a/sub⟧tp→ a b)
    (x F.[ ⟦ b ⟧tp→ ])
to-⊢ {Δ = Δ} {r = r} (r-ivar x) =
  let i , eq = ∈⟶index (VP.List-∈⇒∈ x) in 
      let i' = (subst Fin (sym $ length-map _ Δ) i) in
        subst (λ u → ⟦ Δ ⟧ctx→ F.⊢ (F.var i') ∈ u) (lookup⟦⟧ Δ i eq) (F.var i')
to-⊢ (r-iabs {a = a} p) = F.λ' ⟦ a ⟧tp→ (to-⊢ p)
to-⊢ (r-iapp p p₁) = (to-⊢ p) F.· (to-⊢ p₁)

iso : ∀ {ν} (Δ : ICtx ν) r → Δ ⊢ᵣ r ⇔ (∃ λ t → ⟦ Δ ⟧ctx→ F.⊢ t ∈ ⟦ r ⟧tp→)
iso Δ r = equivalence
  (λ x → , (to-⊢ x))
  (λ x → subst₂ (λ Δ' r' → Δ' ⊢ᵣ r') (ctx→← _) (tp→← r) (from-⊢ (proj₂ x)))
