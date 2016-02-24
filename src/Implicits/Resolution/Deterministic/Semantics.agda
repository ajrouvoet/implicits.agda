open import Prelude
open import Data.List.Properties
open import Data.List.Any hiding (map)

module Implicits.Resolution.Deterministic.Semantics where

open import Implicits.Syntax
open import Implicits.Resolution.Deterministic.Resolution
open import Implicits.Substitutions
open import Implicits.Substitutions.Lemmas
open import Implicits.Semantics
open import Implicits.Semantics.Lemmas
open import Extensions.ListFirst

open import SystemF as F using ()

module DerivationSemantics where

  ⟦_,_⟧r : ∀ {ν n} {K : Ktx ν n} {a} → (proj₂ K) ⊢ᵣ a → K# K →
           ∃ λ t → ⟦ K ⟧ctx→ F.⊢ t ∈ ⟦ a ⟧tp→
  ⟦_,_⟧r {K = K} (r-simp {ρ = r} r∈Δ r↓τ) m with ∈⟶index (All.lookup m (proj₁ $ first⟶∈ r∈Δ))
  ⟦_,_⟧r {K = K} (r-simp {ρ = r} r∈Δ r↓τ) m | i , lookup-i≡r =
    ⟦ subst (λ u → _ F.⊢ F.var i ∈ u) eq (F.var i) , r↓τ , m ⟧r↓
    where
      eq = begin 
        lookup i ⟦ K ⟧ctx→
          ≡⟨ sym $ lookup-⟦⟧ctx→ K i ⟩
        ⟦ lookup i (proj₁ K) ⟧tp→
            ≡⟨ cong ⟦_⟧tp→ lookup-i≡r ⟩
        ⟦ r ⟧tp→ ∎ 

      ⟦_,_,_⟧r↓ : ∀ {ν n} {K : Ktx ν n} {a ta τ} → 
                ⟦ K ⟧ctx→ F.⊢ ta ∈ ⟦ a ⟧tp→ → (proj₂ K) ⊢ a ↓ τ → K# K → 
                ∃ λ tτ → ⟦ K ⟧ctx→ F.⊢ tτ ∈ ⟦ simpl τ ⟧tp→
      ⟦ ⊢ta , i-simp τ , m ⟧r↓ = , ⊢ta
      ⟦ ⊢ta , i-iabs {ρ₁ = a} ⊢ᵣa b↓τ , m ⟧r↓ =
        , (proj₂ ⟦ ⊢ta F.· (proj₂ ⟦ ⊢ᵣa , m ⟧r) , b↓τ , m ⟧r↓)
      ⟦ ⊢ta , i-tabs {ρ = a} b p , m ⟧r↓ =
        ⟦ subst (λ u → _ F.⊢ _ ∈ u) (sym $ ⟦a/sub⟧tp→ a b) (⊢ta F.[ ⟦ b ⟧tp→ ]) , p , m ⟧r↓ 

  ⟦ r-iabs a {ρ₂ = b} ⊢b , m ⟧r = , F.λ' ⟦ a ⟧tp→ (proj₂ ⟦ ⊢b , #ivar a m ⟧r)

  ⟦_,_⟧r {K = K} (r-tabs {ρ = r} p) m with ⟦ p , #tvar m ⟧r
  ⟦_,_⟧r {K = K} (r-tabs {ρ = r} p) m | _ , x =
    , F.Λ (subst (λ u → u F.⊢ _ ∈ ⟦ r ⟧tp→) (⟦weaken⟧ctx→ K) x) 

open Semantics _⊢ᵣ_ DerivationSemantics.⟦_,_⟧r public
