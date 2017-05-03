open import Prelude
open import Data.Vec
open import Data.List.Properties
open import Data.List.Any hiding (map)
open import Data.List.All as All using ()
open import Extensions.Vec
open import Data.Product hiding (map)

module Implicits.Resolution.Ambiguous.Semantics where

open import Implicits.Syntax
open import Implicits.Resolution.Ambiguous.Resolution
open import Implicits.Substitutions
open import Implicits.Substitutions.Lemmas
open import Implicits.Semantics
open import Implicits.Semantics.Lemmas


open import SystemF as F using ()

module DerivationSemantics where

  ⟦_,_⟧r : ∀ {ν n} {Δ} {Γ : Ctx ν n} {a} → Δ ⊢ᵣ a → Γ # Δ →
           ∃ λ t → ⟦ Γ ⟧ctx→ F.⊢ t ∈ ⟦ a ⟧tp→
  ⟦_,_⟧r (r-tabs {r = r} p) m with ⟦ p , #tvar m ⟧r
  ⟦_,_⟧r {Γ = Γ} (r-tabs {r = r} p) m | _ , x =
    , F.Λ (subst (λ u → u F.⊢ _ ∈ ⟦ r ⟧tp→) (⟦weaken⟧ctx→ Γ) x)
  ⟦_,_⟧r (r-tapp a p) m with ⟦ p , m ⟧r
  ⟦_,_⟧r {Γ = Γ} (r-tapp {r = a} b p) m | _ , x =
    , subst
      (λ u → ⟦ Γ ⟧ctx→ F.⊢ _ ∈ u)
      (sym $ ⟦a/sub⟧tp→ a b)
      (x F.[ ⟦ b ⟧tp→ ])
  ⟦_,_⟧r {Γ = Γ} {a = a} (r-ivar x) m with ∈⟶index (All.lookup m x)
  ⟦_,_⟧r {Γ = Γ} {a = a} (r-ivar x) m | i , lookup-i≡r =
    , subst (λ u → _ F.⊢ F.var i ∈ u) eq (F.var i)
    where
      eq = begin
        lookup i ⟦ Γ ⟧ctx→
          ≡⟨ sym $ lookup-⟦⟧ctx→ Γ i ⟩
        ⟦ lookup i Γ ⟧tp→
            ≡⟨ cong ⟦_⟧tp→ lookup-i≡r ⟩
        ⟦ a ⟧tp→ ∎
  ⟦_,_⟧r (r-iabs {a = a} p) m = , F.λ' ⟦ a ⟧tp→ (proj₂ ⟦ p , #ivar a m ⟧r)
  ⟦_,_⟧r (r-iapp p p₁) m = , (proj₂ ⟦ p , m ⟧r) F.· (proj₂ ⟦ p₁ , m ⟧r)

open Semantics _⊢ᵣ_ DerivationSemantics.⟦_,_⟧r public
