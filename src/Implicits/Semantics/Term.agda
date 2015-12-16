open import Prelude

module Implicits.Semantics.Term
  (TC : Set)
  (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Implicits.Syntax TC _tc≟_
open import Implicits.WellTyped TC _tc≟_
open import Implicits.Semantics.Type TC _tc≟_
open import Implicits.Semantics.Context TC _tc≟_
open import Implicits.Semantics.Lemmas TC _tc≟_
open import Implicits.Semantics.RewriteContext TC _tc≟_
open import SystemF TC as F using ()

module TermSemantics
  (_⊢ᵣ_ : ∀ {ν} → ICtx ν → Type ν → Set)
  (⟦_,_⟧r : ∀ {ν n} {K : Ktx ν n} {a} → (proj₂ K) ⊢ᵣ a → K# K →
            ∃ λ t → ⟦ K ⟧ctx→ F.⊢ t ∈ ⟦ a ⟧tp→) where

  open TypingRules _⊢ᵣ_

  -- denotational semantics of well-typed terms
  ⟦_,_⟧ : ∀ {ν n} {K : Ktx ν n} {t} {a : Type ν} → K ⊢ t ∈ a → K# K → F.Term ν n
  ⟦_,_⟧ (var x) m = F.var x
  ⟦_,_⟧ (Λ t) m = F.Λ ⟦ t , #tvar m ⟧
  ⟦_,_⟧ (λ' a x) m = F.λ' ⟦ a ⟧tp→ ⟦ x , #var a m ⟧
  ⟦_,_⟧ (f [ b ]) m = F._[_] ⟦ f , m ⟧ ⟦ b ⟧tp→
  ⟦_,_⟧ (f · e) m = ⟦ f , m ⟧ F.· ⟦ e , m ⟧
  ⟦_,_⟧ (ρ a x) m = F.λ' ⟦ a ⟧tp→ ⟦ x , #ivar a m ⟧
  ⟦_,_⟧ (f ⟨ e∈Δ ⟩) m = ⟦ f , m ⟧ F.· (proj₁ ⟦ e∈Δ , m ⟧r)
  ⟦_,_⟧ (_with'_ r e) m = ⟦ r , m ⟧ F.· ⟦ e , m ⟧
