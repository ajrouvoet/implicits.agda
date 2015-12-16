open import Prelude

module Implicits.Semantics
  (TC : Set)
  (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Implicits.Syntax TC _tc≟_
open import Implicits.WellTyped TC _tc≟_
open import Implicits.Semantics.Type TC _tc≟_ public
open import Implicits.Semantics.Context TC _tc≟_ public
open import Implicits.Semantics.RewriteContext TC _tc≟_ public
open import Implicits.Semantics.Term TC _tc≟_ public
open import Implicits.Semantics.Preservation TC _tc≟_ public

open import SystemF TC as F using ()

module Semantics
  (_⊢ᵣ_ : ∀ {ν} → ICtx ν → Type ν → Set)
  (⟦_,_⟧r : ∀ {ν n} {K : Ktx ν n} {a} → (proj₂ K) ⊢ᵣ a → K# K →
            ∃ λ t → ⟦ K ⟧ctx→ F.⊢ t ∈ ⟦ a ⟧tp→) where

  open TypingRules _⊢ᵣ_
  open TermSemantics _⊢ᵣ_ ⟦_,_⟧r public
  open Preservation _⊢ᵣ_ ⟦_,_⟧r public
